theory Syntax imports Main
begin

lemma simplImpl: "A \<longrightarrow> A"
apply (rule impI)
apply assumption
  done

type_synonym name = string

(* See grammar l. 192 *)
datatype value_type 
  = LongVT | DoubleVT | StringVT | BooleanVT | DatetimeVT 

(* See grammar l. 189 *)
datatype native_type 
  = Attribute
  | Entity
  | Relation
  | Role
  | Thing

datatype tp 
  = NativeTp native_type
  | ValueTp value_type
  | NamedTp name

(* See grammar l. 114 ff 
   TODO: incomplete; missing: Abstract, Regex, Subx, Then, Type, When
*)
datatype tp_rel 
  = Owns | Plays | Relates | Sub


end