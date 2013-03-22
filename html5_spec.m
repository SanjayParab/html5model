-- Sample HTML 5 Specification Murphi model 

--NOTES:
--1. The stack of elements grows downwards; the topmost node on the stack is the first one 
-- added to the stack, and the bottommost node of the stack is the most      
-- recently added node in the stack

--2. The html node, however it is created, is the topmost node of the stack. 
--It only gets popped off the stack when the parser finishes.

--3. The current node is the bottommost node in the stack of elements.

--4. A ruleset can be thought of as syntactic sugar for creating a copy
--   of its component rules for every value of its quantifier.

--5. Mark the element as being "parser-inserted" and unset the element's "force-async" flag.
--This ensures that, if the script is external, any document.write() calls in the script will
--execute in-line, instead of blowing the document away, as would happen in most other cases.
--It also prevents the script from executing until the end tag is seen.

--6. When the insertion mode is switched to "text" or "in table text", the original insertion
--mode is also set. 
--This is the insertion mode to which the tree construction stage will return.  



Const 
  elementCount: 10;
  
Type
  elementID: 1..elementCount;
  int_range: 0..10;

  --tokens from tokenization stage
  token: enum{html,head,body,script,link,style,meta,head_end,body_end,br_end,html_end};    
  
  --tag names for tokens
  tag_name: enum{HTMLHtmlElement,HTMLHeadElement,HTMLLinkElement,HTMLMetaElement,HTMLStyleElement,HTMLScriptElement};

  --insertion mode controls the tree construction stage. 
  mode_type: enum{initial,before_html,before_head,in_head,after_head,in_body,text};

  frameset_tags: enum{not_ok,ok};
  
  element: Record
    ID: elementID; 
    tag: token; 
    tag_name: tag_name;
    insertion_mode: mode_type; 
    orig_insertion_mode: mode_type;
    parser_inserted: boolean;
    force_async: boolean;
    
  End;

Var
  current_node: element;
  head_pointer: int_range;
  stack_pointer: elementID;
  stack_top_element: element;
  frameset_ok_tag: frameset_tags;

  --an array of elements
  elements: Array[elementID] of element; 

  --array to hold DOM tree elements
  DOM_elements: Array[elementID] of element;

  --stack of open elements
  stack_open_elements: Array[elementID] of element;


--Procedures and Functions 
procedure stack_push(e:element);
  begin
    stack_pointer := stack_pointer - 1;
    stack_open_elements[stack_pointer] := e;
    current_node := stack_open_elements[stack_pointer];
  end;

procedure stack_pop();
  begin
    stack_top_element := stack_open_elements[stack_pointer];
    stack_pointer := stack_pointer - 1; 
    current_node := stack_open_elements[stack_pointer];
  end;

procedure set_pointer(t:token; e:elementID);
 begin 
   switch t
     case head:
        head_pointer := e;
   endswitch;
 end;

procedure create_element(t:token; e:elementID);
  begin
    elements[e].ID := e;
    switch t
      case html:
        elements[e].tag_name := HTMLHtmlElement;
      case head:
        elements[e].tag_name := HTMLHeadElement;
      case link:
        elements[e].tag_name := HTMLLinkElement;
      case meta:
        elements[e].tag_name := HTMLMetaElement;
      case style:
        elements[e].tag_name := HTMLStyleElement;
      case script:
        elements[e].tag_name := HTMLScriptElement;
    endswitch;
  end;


-- Rules

Ruleset e:elementID; t:token Do

  Rule "initial insertion mode"
    (elements[e].insertion_mode = initial)
    ==>
    Begin
       switch t
       case html:
           elements[e].tag := t;
           elements[e].insertion_mode := before_html;
       --else
          --parse error
       Endswitch;
    End;


 Rule "before_html insertion mode"
   (elements[e].insertion_mode = before_html)
    ==>
    Begin
       switch t
       
       case html:
         create_element(html, e);

         --append token to document object
         DOM_elements[e].tag := elements[e].tag;
        
         stack_push(elements[e]); 
         elements[e].insertion_mode := before_head;

       case head_end, body_end, html_end, br_end:
         create_element(html, e);

         --append token to document object
         DOM_elements[e].tag := elements[e].tag;

         --The stack grows downwards        
         stack_push(elements[e]); 
         elements[e].insertion_mode := before_head;
       Endswitch;
    Endrule;
    
   Rule "before_head insertion mode"
   (elements[e].insertion_mode = before_head)
    ==>
    Begin
       switch t
       
       case html:
         --parse error;
         --process every attribute and add to top of SOE if not there. not sure if necessary

       case head:
         create_element(html, e);   
         set_pointer(head, e);  
         stack_push(elements[e]); 
         elements[e].insertion_mode := in_head;

       else
         create_element(html, e);   
         set_pointer(head, e);  
         stack_push(elements[e]); 
         elements[e].insertion_mode := in_head;
       endswitch;
   endrule;

   Rule "in_head insertion mode"
   (elements[e].insertion_mode = before_head)
    ==>
    Begin
       switch t
         case html:
           --parse error;
           --process every attribute and add to top of SOE if not there. not sure if necessary

         case link, meta:
           create_element(t, e); 
           stack_push(elements[e]);
          
         case style:
           create_element(t,e);
           stack_push(elements[e]);
           elements[e].orig_insertion_mode := elements[e].insertion_mode;
           elements[e].insertion_mode := text;
         
         case script:
           create_element(t,e);
           elements[e].parser_inserted := true;
           elements[e].force_async := false;
           stack_push(elements[e]);
           elements[e].orig_insertion_mode := elements[e].insertion_mode;
           elements[e].insertion_mode := text;
   
         case head_end:
           stack_pop();
           elements[e].insertion_mode := after_head;

         --case body_end, html_end, br_end:
           --case end_head;

         else
           stack_pop();
           elements[e].insertion_mode := after_head;

       endswitch;
    endrule;

  Rule "after_head insertion mode"
   (elements[e].insertion_mode = after_head)
    ==>
    var x: int_range;

    Begin
       switch t
         case html:
            --parse error;
            --process every attribute and add to top of SOE if not there. not sure if necessary
 
         case body:
            create_element(t,e);
            stack_push(elements[e]);
            frameset_ok_tag := not_ok;
            elements[e].insertion_mode := in_body;

         case meta,link,script,style:
            --parse error
            stack_push(elements[head_pointer]);
            x := stack_pointer;
            
            if t = meta | t = link then
               create_element(t, e); 
               stack_push(elements[e]);

            elsif t = style then
               create_element(t,e);
               stack_push(elements[e]);
               elements[e].orig_insertion_mode := elements[e].insertion_mode;
               elements[e].insertion_mode := text;

            elsif t = script then
               create_element(t,e);
               elements[e].parser_inserted := true;
               elements[e].force_async := false;
               stack_push(elements[e]);
               elements[e].orig_insertion_mode := elements[e].insertion_mode;
               elements[e].insertion_mode := text;
            endif;
            
            --Remove the node pointed to by the head element pointer from the SOE
            --current pointer stored by x.
            --to check with yuva how to remove the node
           
         case body_end, html_end, br_end:
            create_element(t,e);
            stack_push(elements[e]);
            frameset_ok_tag := ok;
            elements[e].insertion_mode := in_body; 

         endswitch;
  endrule;


EndRuleset;


Startstate
  head_pointer := 0;
  stack_pointer := 10;

  undefine DOM_elements;
  undefine stack_open_elements;

  -- clear elements
  For e:elementID Do
    elements[e].insertion_mode := initial;  
    elements[e].parser_inserted := false; 
    elements[e].force_async := true;
  End;
  


EndStartstate;


