-- Sample HTML 5 Specification Murphi model 

Const 
  elementCount: 10;

  
Type
  elementID: 1..elementCount;
  int_range: 0..10;

  --tokens from tokenization stage
  token: enum{script,html};    
  
  --tag names for tokens
  tag_name: enum{HTMLHtmlElement};

  --insertion mode controls the tree construction stage. 
  mode_type: enum{initial,before_html,in_head,in_body,text,before_head};

  
  element: Record
    insertion_mode: mode_type; 
    tag: token; 
    tag_name: tag_name;
    --var data; --not sure of declaration
  End;

Var

  stack_pointer: elementID;
  --stack_bottom: elementID;
  stack_top_element: element;

  --an array of elements
  elements: Array[elementID] of element; 

  --array to hold DOM tree elements
  DOM_elements: Array[elementID] of element;

  --stack of open elements
  open_elements_stack: Array[elementID] of element;


--Procedures and Functions 

function stack_push(ele: element): boolean;
begin
  stack_pointer := stack_pointer - 1;
  elements[stack_pointer] := element;
  return true;
end;

function stack_pop(): element;
begin
  stack_top_element := elements[stack_pointer];
  stack_pointer := stack_pointer - 1;
end;
  
-- Rules

Ruleset e:elementID Do

  Rule "initial insertion mode"
    (elements[e].insertion_mode = initial)
    ==>
    Begin
       switch elements[e].tag
       case html:
          elements[e].insertion_mode := before_html;
       --else
          --parse error
       Endswitch;
    Endrule;


 Rule "before_html insertion mode"
   (elements[e].insertion_mode = before_html)
    ==>
    var x: int_range;
    Begin
       switch elements[e].tag
       
       case html:
         --create an element for token;
         elements[e].tag_name := HTMLHtmlElement;

         --append token to document object
         DOM_elements[e].tag := elements[e].tag;

         --The stack grows downwards
         x := 10;         
         open_elements_stack[x].tag := elements[e].tag; 
         elements[e].insertion_mode := before_head;
         x := x - 1;

        Endswitch;
    Endrule;

EndRuleset;

--NOTES:
--1. The stack grows downwards; the topmost node on the stack is the first one 
-- added to the stack, and the bottommost node of the stack is the most      
-- recently added node in the stack

--2. The html node, however it is created, is the topmost node of the stack. 
--It only gets popped off the stack when the parser finishes.


Startstate
  stack_pointer := 10;
  --stack_bottom := 0;
  -- clear elements
  For e:elementID Do
    elements[e].insertion_mode := initial;   
    elements[e].tag := html; 
  End;
  
  undefine DOM_elements;
  undefine open_elements_stack;

EndStartstate;


