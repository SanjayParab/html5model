-- HTML 5 Specification Murphi model 

/*
NOTES:
1. The stack of elements grows downwards; the topmost node on the stack is the first one added to the stack, and the bottommost node of the stack is the most  recently added node in the stack

2. The html node, however it is created, is the topmost node of the stack. It only gets popped off the stack when the parser finishes.

3. The current node is the bottommost node in the stack of elements.

4. A ruleset can be thought of as syntactic sugar for creating a copy of its component rules for every value of its quantifier.

5. Mark the element as being "parser-inserted" and unset the element's "force-async" flag. This ensures that, if the script is external, any document.write() calls in the script will execute in-line, instead of blowing the document away, as would happen in most other cases. It also prevents the script from executing until the end tag is seen.

6. When the insertion mode is switched to "text" or "in table text", the original insertion mode is also set. This is the insertion mode to which the tree construction stage will return.  

7. Each document has a current document readiness. When the document object is created, it must have its CDR set to "loading" if the document is associated with a HTML,XML parser or XSLT processor, and to "complete" otherwise

*/

----------------------------------------------------------------------------
--Declarations--
----------------------------------------------------------------------------

Const 
  elementCount: 10;
  
Type
  elementID: 0..elementCount-1;
  int_range: 0..10-1;

  --tokens from tokenization stage
  token: enum{
              null,html,head,body,form,button,
              script,link,style,meta,head_end,
              table,td,th,p,thead,tr,tbody,dd,dt,li, --tokens included for in_body checks
              div,
              body_end,form_end,br_end,script_end,
              p_end,div_end,html_end
              };    
  
  --tag names for tokens
  tag_name: enum{
                  HTMLHtmlElement,HTMLHeadElement,HTMLFormElement,
                  HTMLLinkElement,HTMLMetaElement,HTMLStyleElement,
                  HTMLScriptElement
                };

  --insertion mode controls the tree construction stage. 
  mode_type: enum{
                   initial,before_html,before_head,
                   in_head,after_head,in_body,text,
                   after_body
                 };

  frameset_tags: enum{not_ok,ok};
  current_doc_readiness: enum{loading,interactive,complete};
  element_scope: enum{body_scope,button_scope};
  exempted_implied_tag: enum{none,paragraph};
  attribute_type: enum{http_equiv,content,async};
  attribute: array[elementID] of attribute_type; 

  element: Record
    ID: elementID; 
    tag: token; 
    tag_name: tag_name;
    insertion_mode: mode_type; 
    orig_insertion_mode: mode_type;
    parser_inserted: boolean;
    force_async: boolean;
    attribute: array[elementID] of attribute; --2-dim array to hold attribute value
  End;

Var
  current_node: element;
  head_pointer: int_range;
  form_pointer: int_range;
  stack_pointer: elementID;
  stack_top_element: element;
  frameset_ok_tag: frameset_tags;
  empty_element: element;  
  elements: Array[elementID] of element; --an array of elements
  DOM_elements: Array[elementID] of element;--array to hold DOM tree elements
  stack_open_elements: Array[elementID] of element;



-----------------------------------------------------------------------------
--Procedures--
-----------------------------------------------------------------------------

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

procedure remove_stack_element(i:elementID);
  begin
    stack_open_elements[i] := empty_element;   
  end;

procedure set_pointer(t:token; e:elementID);
 begin 
   switch t
     case head:
        head_pointer := e;
    
     case form:
        form_pointer := e;

   endswitch;
 end;

procedure set_current_node(e:element);
 begin
   current_node := e;
 end;

procedure create_element(t:token; e:elementID);
  begin
    elements[e].ID := e;
    switch t
      case html,html_end:
        elements[e].tag_name := HTMLHtmlElement;
      case head,head_end:
        elements[e].tag_name := HTMLHeadElement;
      case form,form_end:
        elements[e].tag_name := HTMLFormElement;
      case link:
        elements[e].tag_name := HTMLLinkElement;
      case meta:
        elements[e].tag_name := HTMLMetaElement;
      case style:
        elements[e].tag_name := HTMLStyleElement;
      case script,script_end:
        elements[e].tag_name := HTMLScriptElement;
    endswitch;
  end;

----------------------------------------------------------------------------
--Functions --
----------------------------------------------------------------------------


function count_stack_elements() : int_range;
  var count:int_range;

  begin
    count := 0;
    for i:int_range do
	if stack_open_elements[i].tag != null then
           count := count + 1;
        endif;
    endfor;
    return count;
  end;

function get_stack_elemID(i:elementID) : element;
  begin
     return stack_open_elements[i];
  end;

function find_element(t:token): element;
var i:elementID;

  begin
    while elements[i].tag != t do
          i := i + 1;
    endwhile;
    return elements[i];
  end;

function is_member(t:token; num:int_range) : boolean;
 var element_type_list : array[elementID] of token; 
 begin
   switch num
      case 1:
           element_type_list[0] := html;
           element_type_list[1] := table;
           element_type_list[2] := td;
           element_type_list[3] := th;
      case 2:
           element_type_list[0] := html;
           element_type_list[1] := body;
           element_type_list[2] := p;
           element_type_list[3] := thead;
           element_type_list[4] := tr;
           element_type_list[5] := th;
           element_type_list[6] := td;
           element_type_list[7] := tbody;
      case 3:
           element_type_list[0] := dd;
           element_type_list[1] := dt;
           element_type_list[2] := li;
      case 4:
           element_type_list[0] := dd;
           element_type_list[1] := dt;
           element_type_list[2] := li;
           element_type_list[2] := p;
   endswitch;

   for i:elementID do
     if t = element_type_list[i] then
        return true;
     else
        return false;
     endif;    
   endfor;
  end;

function element_in_specific_scope(e:element; target:token; s:element_scope): boolean;
  var node : element;
  var action : enum{loop,pass,fail};
  begin  
    node := e;
    set_current_node(node);   
 
    while action = loop do

       if current_node.tag = target then
          action := pass;
       elsif  is_member(current_node.tag,1) then 
          action := fail;
       elsif (s = button_scope) & (current_node.tag = button) then
          action := fail;
       else
          node := stack_open_elements[e.ID+1];
          action := loop;
       endif;
    endwhile;   

    if action = pass then
       return true;
    elsif action = fail then
       return false;
    endif;      
  end;   

function find_element_in_scope(target:token; elem_scope:element_scope): boolean;
var result : array[elementID] of boolean;
  begin
     for i : elementID do 
        result[i] := element_in_specific_scope(stack_open_elements[i],target,elem_scope);           
     
        if result[i] = true then        
           return true;
        else 
           return false;
        endif;
     endfor;
  end;


function accepted_elements_in_stack() : boolean; 
  begin
    for i:elementID do
       if is_member(stack_open_elements[i].tag,2) then
          return true;
       else
          return false;
       endif;
    end;
  end;  

procedure generate_implied_endtags(ex:exempted_implied_tag);
 begin 
    if ex = none then
       if !(is_member(current_node.tag,3)) then 
           stack_pop();
       endif;
    elsif ex = paragraph then
       if !(is_member(current_node.tag,4)) then 
           stack_pop();
       endif;
    endif;

  end;

----------------------------------------------------------------------------
-- Rules--
----------------------------------------------------------------------------

Ruleset e:elementID; t:token Do

----------------------------------------------------------------
--Before HTML section--
----------------------------------------------------------------

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

-------------------------------------------------------------------
--Before Head and Head Section--
-------------------------------------------------------------------
    
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

         case link:
           create_element(t, e); 
           stack_push(elements[e]);
          
         case meta:
           --in progress
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
            
            --Remove node pointed to by the head element pointer from the SOE
            remove_stack_element(x);
           
         case body_end, html_end, br_end:
            create_element(t,e);
            stack_push(elements[e]);
            frameset_ok_tag := ok;
            elements[e].insertion_mode := in_body; 

         endswitch;
  endrule;

----------------------------------------------------------------------
--Body Section--
----------------------------------------------------------------------

 Rule "in_body insertion mode"
   (elements[e].insertion_mode = after_head)
    ==>
    var 
       i,x, stack_count: int_range;
       result,node: element;

    Begin
       switch t
         case html:
            --parse error;
            --process every attribute and add to top of SOE if not there. not sure if necessary
         
         case link,meta,script,style:
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

         case body:
            --parse error
            --check if 2nd element on SOE is not a body element
            x := stack_pointer + 1; 
            result := get_stack_elemID(x);
            stack_count := count_stack_elements();
            if (result.tag != body) | (stack_count = 1) then --fragment case
               --ignore token
            else
               frameset_ok_tag := not_ok;
            endif;

         case body_end:
            if !find_element_in_scope(body,body_scope) then
                --parse error
            elsif !accepted_elements_in_stack() then
                --parse error
            else
              elements[e].insertion_mode := after_body;
            endif;

         case html_end:
             if !find_element_in_scope(body,body_scope) then
                --parse error
             elsif !accepted_elements_in_stack() then
                --parse error
             else
              elements[e].insertion_mode := after_body;
             endif;

         case div,p:
             if find_element_in_scope(p,button_scope) then
                --act as p_end
             else
                create_element(t,e);
                stack_push(elements[e]);
             endif;
        
         case form:
             if form_pointer != 0 then
                --parse error, ignore token
             else
                if find_element_in_scope(p,button_scope) then
                   --act as if p_end had been seen
                   if !find_element_in_scope(p,button_scope) then
                      --parse error
                      create_element(p,e);
                      stack_push(elements[e]);
                   else
                      generate_implied_endtags(paragraph);
                      while current_node.tag_name != elements[e].tag_name do
                        --parse error
                        stack_pop();
                      endwhile;
                      if current_node.tag_name = elements[e].tag_name then
                         stack_pop();
                      endif;
                   endif;
                endif;

                create_element(t,e);
                stack_push(elements[e]);
                set_pointer(form,e);
             endif;

         case div_end:
             if !find_element_in_scope(t,body_scope) then
                --parse error
             else
                generate_implied_endtags(none);

                while current_node.tag_name != elements[e].tag_name do
                   --parse error
                   stack_pop();
                endwhile;
                if current_node.tag_name = elements[e].tag_name then
                   stack_pop();
                endif;
             endif;
   

         case form_end:
               node := elements[form_pointer]; 
               set_pointer(form,0);                
               if (node.ID = 0)  then
                  --parse error
               else
                  generate_implied_endtags(none);
                  if current_node.tag_name != node.tag_name then
                     --parse error
                     remove_stack_element(node.ID);
                  endif;
               endif;           

         case p_end:
              if !find_element_in_scope(p,button_scope) then
                 --parse error
                 create_element(p,e);
                 stack_push(elements[e]);
              else
                 generate_implied_endtags(paragraph);
                 while current_node.tag_name != elements[e].tag_name do
                    --parse error
                    stack_pop();
                 endwhile;
                 if current_node.tag_name = elements[e].tag_name then
                   stack_pop();
                 endif;
              endif;
      endswitch;
  endrule;           
                

EndRuleset;


Startstate
  head_pointer := 0;
  form_pointer := 0;
  stack_pointer := 10;

  undefine DOM_elements;
  undefine stack_open_elements;

  -- clear elements
  For e:elementID Do
    elements[e].insertion_mode := initial;  
    elements[e].parser_inserted := false; 
    elements[e].force_async := true;
  End;

  empty_element := elements[0];


EndStartstate;


