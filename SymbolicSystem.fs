module SymbolicSystem 

open System
open System.Collections.Generic

open Util
open TransitionSystem

exception private NotWellFormedException of String

exception SystemConstructionException of String

exception private TypeInferenceException of String
exception private EvaluationCyclicDependenciesException
exception private EvaluationUndefinedVariableException of string

type Constant = 
    | BoolConstant of bool
    | IntConstant of int 

type VariableValue = 
    | IntValue of int
    | BoolValue of bool

module VariableValue = 
    let print (v : VariableValue) = 
        match v with 
        | BoolValue b -> if b then "true" else "false"
        | IntValue i -> string i 

    let printList (v : list<VariableValue>) = 
        v |> List.map print |> Util.combineStringsWithSeperator "," |> fun x -> "{" + x + "}"
       
    let toConstant  (v : VariableValue) =  
        match v with 
        | BoolValue b -> BoolConstant b
        | IntValue i -> IntConstant i


type VariableType = 
    | BoolType 
    | IntType of Set<int> // A type is always finite

module VariableType =

    let rec print (t : VariableType) = 
        match t with 
        | BoolType -> "bool"
        | IntType l -> "{" + (l |> Set.toList |> List.map string |> Util.combineStringsWithSeperator ",") + "}"

    let allValues (t : VariableType) = 
        match t with 
            | BoolType -> 
                [true; false]
                |> List.map BoolValue
            | IntType l -> 
                l |> Set.toList |> List.map IntValue

    let joinTypes t1 t2 = 
        match t1, t2 with 
            | BoolType, BoolType -> 
                Some BoolType
            | IntType l1, IntType l2 -> 
                IntType (Set.union l1 l2)
                |> Some
            | _ -> 
                None

    let intersectTypes t1 t2 = 
        match t1, t2 with 
            | BoolType, BoolType -> 
                Some BoolType
            | IntType l1, IntType l2 -> 
                IntType (Set.intersect l1 l2)
                |> Some
            | _ -> 
                None

    let haveSameBaseType t1 t2 = 
        match t1, t2 with 
            | BoolType, BoolType -> true
            | IntType _, IntType _ -> true
            | _ -> false

    let isValueOfType v t = 
        match v, t with 
            | BoolValue _ , BoolType -> 
                true 
            | IntValue x, IntType s -> Set.contains x s
            | _, _ -> false


type Identifier = String

type Expression = 
    | Var of Identifier 
    | Const of Constant 
    //
    | Neg of Expression
    | And of Expression * Expression
    | Or of Expression * Expression
    | Implies of Expression * Expression
    | Equiv of Expression * Expression
    //
    | Eq of Expression * Expression
    | Neq of Expression * Expression
    //
    | Lt of Expression * Expression
    | Gt of Expression * Expression
    | Leq of Expression * Expression
    | Geq of Expression * Expression
    //
    | UnaryMinus of Expression
    | Add of Expression * Expression
    | Sub of Expression * Expression
    | Mul of Expression * Expression
    | Div of Expression * Expression
    | Mod of Expression * Expression
    //
    | ToBool of Expression
    | ToInt of Expression
    //
    | SetUnion of Expression * Expression
    | SetExp of list<Expression>
    //
    | Ite of Expression * Expression * Expression
    | Case of list<Expression * Expression>

module Expression =
    
    let rec allVars (e : Expression) =
        match e with 
        | Var s -> Set.singleton s
        | Const _ -> Set.empty
        | Eq(e1, e2) 
        | Neq(e1, e2) 
        | Leq(e1, e2) 
        | Geq(e1, e2) 
        | Lt(e1, e2) 
        | Gt(e1, e2) 
        | And(e1, e2) 
        | Or(e1, e2) 
        | Implies(e1, e2) 
        //
        | Add(e1, e2) 
        | Sub(e1, e2) 
        | Mul(e1, e2) 
        | Div(e1, e2) 
        | Mod(e1, e2) 
        | Equiv(e1, e2)
        | SetUnion(e1, e2)  -> 
            Set.union (allVars e1) (allVars e2)
        | Neg e 
        | UnaryMinus e
        | ToBool e
        | ToInt e -> allVars e
        | SetExp l -> 
            l
            |> List.map allVars
            |> Set.unionMany
        | Ite (e1, e2, e3) -> 
            [allVars e1; allVars e2; allVars e3]
            |> Set.unionMany
        | Case l ->
            l
            |> List.map (fun (x, y) -> Set.union (allVars x) (allVars y))
            |> Set.unionMany

    let rec print (e : Expression) = 
        match e with 
        | Var s -> s 
        | Const a -> 
            match a with 
                | BoolConstant b -> "(" + string(b) + ")" 
                | IntConstant i -> "(" + string(i) + ")" 
        | Eq(e1, e2) -> 
            "(=" + print e1 + "," + print e2 + ")"
        | Neq(e1, e2) -> 
            "(!=" + print e1 + "," + print e2 + ")"
        | Leq(e1, e2) -> 
            "(<=" + print e1 + "," + print e2 + ")"
        | Geq(e1, e2) -> 
            "(>=" + print e1 + "," + print e2 + ")"
        | Lt(e1, e2) -> 
            "(<" + print e1 + "," + print e2 + ")"
        | Gt(e1, e2) -> 
            "(>" + print e1 + "," + print e2 + ")"
        | And(e1, e2) -> 
            "(&" + print e1 + "," + print e2 + ")"
        | Or(e1, e2) -> 
            "(|" + print e1 + "," + print e2 + ")"
        | Equiv(e1, e2) -> 
            "(|" + print e1 + "," + print e2 + ")"
        | Implies(e1, e2) -> 
            "(->" + print e1 + "," + print e2 + ")"
        | UnaryMinus e -> 
            "(-" + print e  + ")"
        | Add(e1, e2) -> 
            "(+" + print e1 + "," + print e2 + ")"
        | Sub(e1, e2) -> 
            "(-" + print e1 + "," + print e2 + ")"
        | Mul(e1, e2) -> 
            "(-" + print e1 + "," + print e2 + ")"
        | Div(e1, e2) -> 
            "(-" + print e1 + "," + print e2 + ")"
        | Mod(e1, e2) -> 
            "(-" + print e1 + "," + print e2 + ")"
        | SetUnion(e1, e2) -> 
            "(" + print e1 + " union " + print e2 + ")"
        | Neg e -> 
            "(!" + print e + ")"
        | ToBool e -> 
            "(toBool" + print e + ")"
        | ToInt e -> 
            "(toInt" + print e + ")"
        | SetExp l -> 
            "({" + (l |> List.fold (fun s a -> s + print a) "")  + "})"
        | Ite(e1, e2, e3) -> 
            "(" + print e1 + " ? " + print e2 + " : " + print e3 + "})"
        | Case l -> 
            "(case { \n" + (l |> List.fold (fun s (g, e) -> s + print g + " : " + print e + "\n") "") + "}esac)"


    let rec inferType (env : String -> VariableType) (e : Expression) = 
        match e with 
        | Var s -> env s
        | Const x -> 
            match x with 
                | BoolConstant _ -> BoolType
                | IntConstant i -> IntType (Set.singleton i)
        | Eq(e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | IntType _, IntType _ -> BoolType
            | BoolType, BoolType -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be compared with '='"

        | Neq (e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | IntType _, IntType _ -> BoolType
            | BoolType, BoolType -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be compared with '!='"

        // ================================== Compare ==================================
        | Leq (e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | IntType _, IntType _ -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be compared with '<='"

        | Geq(e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | IntType _, IntType _ -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be compared with '>='"

        | Lt(e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | IntType _, IntType _ -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be compared with '<'"

        | Gt(e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | IntType _, IntType _ -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be compared with '>'"

        // ================================== Boolean ==================================
        | And(e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | BoolType, BoolType -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be combined with '&'"

        | Or(e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | BoolType, BoolType -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be combined with '|'"

        | Implies(e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | BoolType, BoolType -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be combined with '->'"

        | Equiv(e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | BoolType, BoolType -> BoolType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be combined with '<->'"

        | Neg e ->
            match inferType env e with 
            | BoolType -> BoolType
            | t -> raise <| SystemConstructionException $"Expression %s{print e} (of type %s{VariableType.print t}) cannot be combined with '!'"

        // ================================== Arithmetic ==================================
        | UnaryMinus e -> 
            match inferType env e with 
            | IntType s -> s |> Set.map (fun x -> x - 1) |> IntType
            | t -> raise <| SystemConstructionException $"Expressions %s{print e} (of type %s{VariableType.print t}) cannot be combined with '-'"
        | Add(e1, e2) -> 
            match inferType env e1, inferType env e2 with 
            | IntType s1, IntType s2 -> 
                Seq.allPairs s1 s2 
                |> Seq.map (fun (a, b) -> a + b)
                |> set 
                |> IntType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be combined with '+'"
        | Sub(e1, e2) -> 
            match inferType env e1, inferType env e2  with 
            | IntType s1, IntType s2 -> 
                Seq.allPairs s1 s2 
                |> Seq.map (fun (a, b) -> a - b)
                |> set 
                |> IntType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be combined with '-'"
        | Mul(e1, e2) -> 
            match inferType env e1, inferType env e2  with 
            | IntType s1, IntType s2 -> 
                Seq.allPairs s1 s2 
                |> Seq.map (fun (a, b) -> a * b)
                |> set 
                |> IntType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be combined with '*'"
        | Div(e1, e2) -> 
            match inferType env e1, inferType env e2  with 
            | IntType s1, IntType s2 -> 
                Seq.allPairs s1 s2 
                |> Seq.map (fun (a, b) -> a / b)
                |> set 
                |> IntType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be combined with '/'"
        | Mod(e1, e2) -> 
            match inferType env e1, inferType env e2  with 
            | IntType s1, IntType s2 -> 
                Seq.allPairs s1 s2 
                |> Seq.map (fun (a, b) -> if a = 0 || b = 0 then 0 else a % b)
                |> set 
                |> IntType
            | t1, t2 -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t1}) and %s{print e2} (of type %s{VariableType.print t2}) cannot be combined with 'mod'"

        // ==================================  ==================================
        | SetExp e -> 
            e 
            |> List.map (fun x -> inferType env x)
            |> List.reduce (fun t1 t2 -> 
                match VariableType.joinTypes t1 t2 with 
                | Some t -> t
                | None -> 
                    raise <| SystemConstructionException $"Could not type set-expression: \n %s{print (SetExp e)}\n Failed to join types %s{VariableType.print t1} and %s{VariableType.print t2}"
                )
        | Ite(e1: Expression, e2, e3) -> 
            match inferType env e1, inferType env e2, inferType env e3  with 
            | BoolType, t1, t2 -> 
                match VariableType.joinTypes t1 t2 with 
                | Some t -> t
                | None -> 
                    raise <| SystemConstructionException $"Could not type '_ ? _ : _'  expression: \n %s{print (Ite(e1, e2, e3))}\n Failed to join types %s{VariableType.print t1} and %s{VariableType.print t2}"

            | t, _, _ -> raise <| SystemConstructionException $"Expressions %s{print e1} (of type %s{VariableType.print t}) is not allowed in guar of '_ ? _ : _' statement"
        | SetUnion(e1, e2) -> 
            match inferType env e1, inferType env e2  with 
            | t1, t2 -> 
                match VariableType.joinTypes t1 t2 with 
                | Some t ->  t
                | None -> raise <| SystemConstructionException $"Could not type expression: \n %s{print (SetUnion(e1, e2))}\n Failed to join types %s{VariableType.print t1} and %s{VariableType.print t2}"
        | ToBool e -> 
            match inferType env e with 
            | IntType _ -> BoolType
            | _ -> raise <| SystemConstructionException $"Could not type expression: \n %s{print (ToBool e)}"
        | ToInt e -> 
            match inferType env e with 
            | BoolType -> IntType ([0; 1] |> set)
            | _ -> raise <| SystemConstructionException $"Could not type expression: \n %s{print (ToInt e)}"
        | Case (cases) -> 
            if cases |> List.exists (fun (g, _) -> inferType env g <> BoolType) then 
                raise <| SystemConstructionException $"Guard Expression does not have boolean type"
            else 
                cases 
                |> List.map (fun (_, e) -> inferType env e)
                |> List.reduce (fun t1 t2 -> 
                    match VariableType.joinTypes t1 t2 with 
                        | Some t -> t
                        | None -> 
                            raise <| SystemConstructionException $"Could not type case-expression: \n %s{print (Case cases)}\n Failed to join types %s{VariableType.print t1} and %s{VariableType.print t2}."
                    )

   
    let rec eval (env : string -> Set<VariableValue>) (e : Expression) = 
        match e with 
        | Var name -> env name
        | Const x -> 
            match x with 
            | IntConstant i -> Set.singleton (IntValue i)
            | BoolConstant b -> Set.singleton (BoolValue b)
        | SetUnion(e1, e2) -> 
            Set.union (eval env e1) (eval env e2)

        | Eq(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> BoolValue (i1 = i2)
                | BoolValue b1, BoolValue b2 -> BoolValue (b1 = b2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Eq(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Neq(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> BoolValue (i1 <> i2)
                | BoolValue b1, BoolValue b2 -> BoolValue (b1 <> b2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Neq(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set

        | Leq(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> BoolValue (i1 <= i2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Leq(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Geq(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> BoolValue (i1 >= i2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Geq(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Lt(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> BoolValue (i1 < i2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Lt(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Gt(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> BoolValue (i1 > i2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Gt(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
            
        | And(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | BoolValue b1, BoolValue b2 -> BoolValue (b1 && b2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (And(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Or(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | BoolValue b1, BoolValue b2 -> BoolValue (b1 || b2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Or(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Implies(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | BoolValue b1, BoolValue b2 -> BoolValue (not b1 || b2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Implies(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Equiv(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | BoolValue b1, BoolValue b2 -> BoolValue ((b1 && b2) || (not b1 && not b2))
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Equiv(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Neg e ->
            eval env e 
            |> Set.map (fun v -> 
                match v with 
                | BoolValue b -> BoolValue (not b)
                | v -> raise <| SystemConstructionException $"Could not eval %s{print (Neg e)} for value %s{VariableValue.print v}"
            )

        | UnaryMinus e -> 
            eval env e 
            |> Set.map (fun v -> 
                match v with 
                | IntValue i -> IntValue -i
                | v -> raise <| SystemConstructionException $"Could not eval %s{print (UnaryMinus e)} for value %s{VariableValue.print v}"
            )
        | Add(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> IntValue(i1 + i2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Add(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Sub(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> IntValue(i1 - i2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Sub(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Mul(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> IntValue(i1 * i2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Mul(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Div(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> IntValue(i1 / i2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Div(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set
        | Mod(e1, e2) -> 
            (eval env e1 |> Set.toList, eval env e2 |> Set.toList)
            ||> List.allPairs
            |> List.map (fun (v1, v2) -> 
                match v1, v2 with 
                | IntValue i1, IntValue i2 -> IntValue(i1 % i2)
                | v1, v2 -> raise <| SystemConstructionException $"Could not eval %s{print (Mod(e1, e2))} for values %s{VariableValue.print v1} and %s{VariableValue.print v2}"
                )
            |> set

        | SetExp e -> 
            e 
            |> List.map (fun x -> eval env x)
            |> Set.unionMany
        | Ite(e1, e2, e3) -> 
            [eval env e1; eval env e2; eval env e3]
            |> List.map seq
            |> Util.cartesianProduct
            |> Seq.toList
            |> List.map (fun vl -> 
                match vl with 
                | [BoolValue b; v1; v2] -> 
                    if b then v1 else v2 
                | _ -> raise <| SystemConstructionException $"Could not eval %s{print (Ite(e1, e2, e3))} as the guard evaluates to %s{VariableValue.printList vl}"
                )
            |> set
        | ToBool e -> 
            eval env e 
            |> Set.map (fun v -> 
                match v with 
                | IntValue i -> if i = 0 then BoolValue false else BoolValue true 
                | v -> raise <| SystemConstructionException $"Could not eval %s{print (ToBool e)} for value %s{VariableValue.print v}"
                )
        | ToInt e -> 
            eval env e 
            |> Set.map (fun v -> 
                match v with 
                | BoolValue b -> if b then IntValue 0 else IntValue 1 
                | v -> raise <| SystemConstructionException $"Could not eval %s{print (ToInt e)} for value %s{VariableValue.print v}"
            )
        | Case cases -> 
            let firstHit = 
                cases
                |> List.tryFind (fun (g, _) -> eval env g = Set.singleton (BoolValue true))

            match firstHit with 
                | None ->
                    raise <| SystemConstructionException $"Could not eval %s{print (Case(cases))} as no case was matched"
                | Some (_, e) -> 
                    eval env e
    
type SymbolicSystem = 
    {
        VarTypes : list<Identifier * VariableType>;
        Init : list<Identifier * Expression>
        Next : list<Identifier * Expression>
        Define : list<Identifier * Expression>
    }

module SymbolicSystem =

    let private inferTypeOfExpression (symbolicSystem : SymbolicSystem) (e : Expression) =  
        let typeMap = symbolicSystem.VarTypes |> Map.ofList
        let defineMap = symbolicSystem.Define |> Map.ofList

        let rec inferType (seenVars: Set<String>) (e : Expression) =
            e 
            |> Expression.inferType (fun x -> 
                if Set.contains x seenVars then 
                    raise <| TypeInferenceException $"Cycle found during type checking"

                if typeMap.ContainsKey x then 
                    typeMap.[x]
                elif Map.containsKey x defineMap then 
                    inferType (Set.add x seenVars) defineMap.[x]
                else 
                    raise <| TypeInferenceException $"Variable %s{x} is neither declared nor is it defined"
                )

        inferType Set.empty e

    

    let private evaluateExpression (symbolicSystem : SymbolicSystem) (state : Map<String, Set<VariableValue>>) (e : Expression) =  
        let typeMap = symbolicSystem.VarTypes |> Map.ofList
        let defineMap = symbolicSystem.Define |> Map.ofList

        let rec eval (seenVars: Set<String>) (state : Map<String, Set<VariableValue>>) (e : Expression) = 
            e 
            |> Expression.eval (fun x -> 
                if Set.contains x seenVars then 
                    raise <| EvaluationCyclicDependenciesException

                if typeMap.ContainsKey x then 
                    // This var should be in the system
                    if Map.containsKey x state then 
                        state.[x]
                    else 
                        raise <| EvaluationUndefinedVariableException x
                elif Map.containsKey x defineMap then 
                    eval (Set.add x seenVars) state defineMap.[x]
                else 
                    raise <| EvaluationUndefinedVariableException x
                )

        eval Set.empty state e



    let findError (symbolicSystem : SymbolicSystem) = 
        try 
            symbolicSystem.VarTypes
            |> List.countBy fst
            |> List.iter (fun (x, i) -> 
                if i > 1 then 
                    raise <| NotWellFormedException $"Type for variable %s{x} is defined more than once"
                ) 

            symbolicSystem.Init
            |> List.countBy fst
            |> List.iter (fun (x, i) -> 
                if i > 1 then 
                    raise <| NotWellFormedException $"Initial value for variable %s{x} is defined more than once"
                ) 

            symbolicSystem.Next
            |> List.countBy fst
            |> List.iter (fun (x, i) -> 
                if i > 1 then 
                    raise <| NotWellFormedException $"Next expression for variable %s{x} is defined more than once"
                ) 

            symbolicSystem.Define
            |> List.countBy fst
            |> List.iter (fun (x, i) -> 
                if i > 1 then 
                    raise <| NotWellFormedException $"Define expression for variable %s{x} is given more than once"
                ) 

            let typeMap = symbolicSystem.VarTypes |> Map.ofList
            let initMap = symbolicSystem.Init |> Map.ofList
            let nextMap = symbolicSystem.Next |> Map.ofList
            let defineMap = symbolicSystem.Define |> Map.ofList

            let vars = 
                symbolicSystem.VarTypes |> List.map fst |> set

            defineMap
            |> Map.iter (fun _ e -> 
                inferTypeOfExpression symbolicSystem e 
                |> ignore
                )

            vars
            |> Set.iter (fun x -> 
                if Map.containsKey x typeMap |> not then 
                    raise <| NotWellFormedException $"Type for variable %s{x} is not defined"

                if Map.containsKey x initMap |> not then 
                    printfn $"Warning: No init condition for variable %s{x}"

                if Map.containsKey x nextMap |> not then 
                    printfn $"Warning: No next condition for variable %s{x}"
                )

            vars
            |> Set.filter (fun x -> initMap.ContainsKey x)
            |> Set.iter (fun name -> 
                let t = typeMap.[name]

                let infert = 
                    try 
                        inferTypeOfExpression symbolicSystem initMap.[name] 
                    with 
                        | TypeInferenceException err -> 
                            raise <| NotWellFormedException $"Error when infering type of the init expression for variable %s{name}: %s{err}"

                if VariableType.haveSameBaseType infert t |> not then 
                    raise <| NotWellFormedException $"The init expression for variable %s{name} has type %s{VariableType.print infert} but the type should be %s{VariableType.print t}"
             
            )

            vars
            |> Set.filter (fun x -> nextMap.ContainsKey x)
            |> Set.iter (fun name -> 
                let t = typeMap.[name]

                let infert = 
                    try 
                        inferTypeOfExpression symbolicSystem nextMap.[name] 
                    with 
                        | TypeInferenceException err -> 
                            raise <| NotWellFormedException $"Error when infering type of the next expression for variable %s{name}: %s{err}"

                if VariableType.haveSameBaseType infert t |> not then 
                    raise <| NotWellFormedException $"The next expression for variable %s{name} has type %s{VariableType.print infert} but the type should be %s{VariableType.print t}"
            )

            None
        with 
            | NotWellFormedException msg -> 
                Some msg


    let convertSymbolicSystemToTSWithHaltingExpression (symbolicSystem : SymbolicSystem) (haltExpression : Expression) (expressionList : list<Expression>) = 

        let vars = symbolicSystem.VarTypes |> List.map fst |> set

        let typeMap = symbolicSystem.VarTypes |> Map.ofList
        let initMap = symbolicSystem.Init |> Map.ofList
        let nextMap = symbolicSystem.Next |> Map.ofList

        let allStates = new HashSet<_>()
        let queue = new Queue<_>()
        let edgeDict = new Dictionary<_,_>()
        let apEvalDict = new Dictionary<_,_>()  

        let initStates = 
            vars
            |> Set.toList
            |> List.map (fun name -> 
                let possibleInitValues = 
                    if Map.containsKey name initMap then 
                        try 
                            evaluateExpression symbolicSystem Map.empty initMap.[name]
                        with 
                            | EvaluationCyclicDependenciesException -> 
                                raise <| SystemConstructionException $"Cyclic Dependency detected when evaluating initial expression for variable %s{name}"
                            | EvaluationUndefinedVariableException x -> 
                                // the init condition for 'name' uses 'x'. If this is a system varaible it is fine, otherwise we report an erro
                                if Map.containsKey x typeMap then 
                                    // We allow something like init(x) = y
                                    // Here we then return all possible values and later filter all possible combinations
                                    VariableType.allValues typeMap.[name] |> set
                                else 
                                    raise <| SystemConstructionException $"Undefined variable %s{x} encountered when evaluating initial expression for variable %s{name}"
                    else 
                        // No initial condition for `name` defined. We use all possible values
                        VariableType.allValues typeMap.[name] |> set

                possibleInitValues
                |> Set.iter (fun v -> 
                    if VariableType.isValueOfType v typeMap.[name] |> not then 
                        raise <| SystemConstructionException $"The value of the initial expression for variable %s{name} is %s{VariableValue.print v} which does not match {VariableType.print typeMap.[name]}"
                    )

                name, possibleInitValues
                )
            |> Map
            |> Util.cartesianProductMap
            |> Seq.filter (fun state -> 
                // We now re-check the initial conditions for all varaibles (this is only needed when some initial condition uses other varaibles, but we always check it as it is cheap)
                vars 
                |> Set.forall (fun name -> 
                    let possibleInitValues = 
                        if Map.containsKey name initMap then 
                            // An initial condition is defined, we evaluate this expression in the current state
                            try 
                                evaluateExpression symbolicSystem (state |> Map.map (fun _ v -> Set.singleton v)) initMap.[name]
                            with 
                                | EvaluationCyclicDependenciesException -> 
                                    raise <| SystemConstructionException $"Cyclic Dependency detected when evaluating initial expression for variable %s{name}"
                                | EvaluationUndefinedVariableException x -> 
                                    raise <| SystemConstructionException $"Undefined variable %s{x} encountered when evaluating initial expression for variable %s{name}"
                        else 
                            // No initial constraint
                            VariableType.allValues typeMap.[name] |> set

                    // Keep this state if the current value is within the allowed values
                    Set.contains state.[name] possibleInitValues
                    )
                )
            |> HashSet

        for s in initStates do
            queue.Enqueue s
            allStates.Add s |> ignore

        while queue.Count <> 0 do 
            let state = queue.Dequeue()

            // We eval the halt proposition to check if we can halt here
            let hasHalted = 
                try 
                    evaluateExpression symbolicSystem (state |> Map.map (fun _ v -> Set.singleton v)) haltExpression 
                with 
                    | EvaluationCyclicDependenciesException -> 
                        raise <| SystemConstructionException $"Cyclic Dependency detected when evaluating halting expression"
                    | EvaluationUndefinedVariableException x -> 
                        raise <| SystemConstructionException $"Undefined variable %s{x} encountered when evaluating halting expression"
                
                |> Set.toList
                |> function 
                    | [BoolValue b] -> b 
                    | v -> raise <| SystemConstructionException $"Halting expression %s{Expression.print haltExpression} evlautes to the non-boolean value %s{VariableValue.printList v}"

            let allSucs = 
                if hasHalted then 
                    // Halted, so we loop in this state
                    Set.singleton state
                else
                    vars
                    |> Set.toList
                    |> List.map (fun name -> 
                        let nextValues = 
                            
                            if Map.containsKey name nextMap then 
                                try 
                                    evaluateExpression symbolicSystem (state |> Map.map (fun _ v -> Set.singleton v)) nextMap.[name] 
                                with 
                                    | EvaluationCyclicDependenciesException -> 
                                        raise <| SystemConstructionException $"Cyclic Dependency detected when evaluating the next expression for variable %s{name}"
                                    | EvaluationUndefinedVariableException x -> 
                                        raise <| SystemConstructionException $"Undefined variable %s{x} encountered when evaluating the next expression for variable %s{name}"
                            else 
                                // No next condition given, so we return all values
                                VariableType.allValues typeMap.[name] |> set

                        nextValues 
                        |> Set.iter (fun v -> 
                            if VariableType.isValueOfType v typeMap.[name] |> not then 
                                raise <| SystemConstructionException $"The value of the next expression for variable %s{name} is %s{VariableValue.print v} which does not match the type of %s{name} (VariableType.print typeMap.[name])"
                            )

                        name, nextValues
                        )
                    |> Map
                    |> Util.cartesianProductMap
                    |> set

            let apEval = 
                expressionList
                |> List.indexed 
                |> List.filter (fun (i, e) -> 
                    try 
                        evaluateExpression symbolicSystem (state |> Map.map (fun _ v -> Set.singleton v)) e
                    with 
                        | EvaluationCyclicDependenciesException -> 
                            raise <| SystemConstructionException $"Cyclic Dependency detected when evaluating the %i{i}th AP-expression"
                        | EvaluationUndefinedVariableException x -> 
                            raise <| SystemConstructionException $"Undefined variable %s{x} encountered when evaluating the %i{i}th AP-expression"
                    |> Set.toList
                    |> function 
                        | [BoolValue b] -> b 
                        | v ->
                            raise <| SystemConstructionException $"The %i{i}th AP-expression evaluates to the non-boolean value %s{VariableValue.printList v}"
                    )
                |> List.map fst 
                |> set

            edgeDict.Add(state, allSucs)
            apEvalDict.Add(state, apEval)

            for s in allSucs do 
                if allStates.Contains s |> not then 
                    queue.Enqueue s
                    allStates.Add s |> ignore

        let allStates = allStates |> set 

        let edgeMap = 
            edgeDict
            |> Util.dictToMap
        
        let apEvalMap = 
            apEvalDict
            |> Util.dictToMap

        let renamingDict = 
            allStates
            |> Seq.mapi (fun i x -> x, i)
            |> Map.ofSeq
    
        {
            States = 
                renamingDict.Values |> set
            InitialStates = 
                initStates
                |> Seq.map (fun x -> renamingDict.[x])
                |> set
            APs = expressionList
            Edges = 
                edgeMap 
                |> Map.toSeq
                |> Seq.map (fun (k, v) -> renamingDict[k], Set.map (fun x -> renamingDict[x]) v)
                |> Map.ofSeq
            ApEval = 
                apEvalMap
                |> Map.toSeq
                |> Seq.map (fun (k, v) -> renamingDict[k], v)
                |> Map.ofSeq
        }

    let convertSymbolicSystemToTS (symbolicSystem : SymbolicSystem) (expressionList : list<Expression>) = 
        convertSymbolicSystemToTSWithHaltingExpression symbolicSystem (Expression.Const (BoolConstant false)) expressionList


module Parser = 
    open FParsec
    
    let private commentParser =
        (skipString "--" .>> restOfLine false)

    let private ws = spaces .>> sepEndBy commentParser spaces

    type private A = 
        | Init of Identifier * Expression
        | Next of Identifier * Expression
        | Define of Identifier * Expression

    let private keywords = 
        [
            "MODULE"
            "ASSIGN"
            "VAR"
            "DEFINE"
            "init"
            "next"
            "TRUE"
            "FALSE"
            "case"
            "esac"
            "min"
            "max"
            "array"
            "of"
            "boolean"
            "mod"
            "union"
            "xor"
            "nxor"
        ]

    let private identifierParser = 
        attempt(
            (letter <|> pchar '_') .>>. manyChars (letter <|> digit <|> pchar '_' <|> pchar '$' <|> pchar '#' <|> pchar '-' <|> pchar '.' <|> pchar '[' <|> pchar ']') 
            >>= fun (x, y) -> (
                let s = string(x) + y
                if List.contains s keywords then 
                    fail ""
                else 
                    preturn s
                )
        )
        
    let private expParser = 
        let expParser, expParserRef = createParserForwardedToRef()

        let constantParser = 
            choice [
                stringReturn "TRUE" (BoolConstant true)
                stringReturn "FALSE" (BoolConstant false)
                pint32 |>> IntConstant
            ]
            |>> Const
            
        let variableParser = 
            identifierParser |>> Var

        let parParser = 
            skipChar '(' >>. ws >>. expParser .>> ws .>> skipChar ')'

        let setParser = 
            pchar '{' >>. sepBy (expParser .>> ws) (pchar ',' .>> ws) .>> pchar '}'
            |>> SetExp

        let caseParser = 
            pstring "case" >>. ws >>.
            sepEndBy (expParser .>> ws .>> pchar ':' .>> ws .>>. expParser) (pchar ';' .>> ws)
            .>> ws .>> pstring "esac"
            |>> Case

        let toIntParser = 
            skipString "toInt" >>. ws >>. skipChar '(' >>. ws >>. expParser .>> ws .>> skipChar ')'
            |>> ToInt

        let toBoolParser = 
            skipString "toBool" >>. ws >>. skipChar '(' >>. ws >>. expParser .>> ws .>> skipChar ')'
            |>> ToBool

        let basicParser = 
            ws >>. choice [ 
                caseParser
                toIntParser
                toBoolParser
                constantParser
                setParser
                parParser
                variableParser
            ] .>> ws

        let oppParser = new OperatorPrecedenceParser<Expression, unit, unit>()

        let addInfixOperator string precedence associativity f =
            oppParser.AddOperator(
                InfixOperator(string, ws, precedence, associativity, f)
            )

        let addPrefixOperator string precedence associativity f =
            oppParser.AddOperator(
                PrefixOperator(string, ws, precedence, associativity, f)
            )   

        let addTernaryOperator leftString rightString precedence associativity f =
            oppParser.AddOperator(
                TernaryOperator(leftString, ws, rightString, ws, precedence, associativity, f)
            )        

        do
            oppParser.TermParser <- basicParser

            addInfixOperator "->" 10 Associativity.Right (fun x y -> Implies(x, y))
            addInfixOperator "<->" 20 Associativity.None (fun x y -> Equiv(x, y))

            addTernaryOperator "?" ":" 30 Associativity.None (fun a b c -> Ite(a, b, c))

            addInfixOperator "|" 40 Associativity.Left (fun x y -> Or(x, y))

            addInfixOperator "&" 50 Associativity.Left (fun x y -> And(x, y))
            
            
            addInfixOperator "=" 60 Associativity.Left (fun x y -> Eq(x, y))
            addInfixOperator "!=" 60 Associativity.Left (fun x y -> Neq(x, y))
            addInfixOperator "<=" 60 Associativity.Left (fun x y -> Leq(x, y))
            addInfixOperator ">=" 60 Associativity.Left (fun x y -> Geq(x, y))
            addInfixOperator "<" 60 Associativity.Left (fun x y -> Lt(x, y))
            addInfixOperator ">" 60 Associativity.Left (fun x y -> Gt(x, y))

            addInfixOperator "union" 70 Associativity.Left (fun x y -> SetUnion(x, y))

            addInfixOperator "+" 80 Associativity.Left (fun x y -> Add(x, y))
            addInfixOperator "-" 80 Associativity.Left (fun x y -> Sub(x, y))

            addInfixOperator "*" 90 Associativity.Left (fun x y -> Mul(x, y))
            addInfixOperator "/" 90 Associativity.Left (fun x y -> Div(x, y))
            addInfixOperator "mod" 90 Associativity.Left (fun x y -> Mod(x, y))

            addPrefixOperator "-" 100 true (fun x -> UnaryMinus x)

            addPrefixOperator "!" 110 true (fun x -> Neg x)

        do 
            expParserRef.Value <- oppParser.ExpressionParser

        expParser

    // Temporary Type that supports arrays and will be used to unfold array types
    type private TempVariableType = 
        | TempBoolType 
        | TempArrayType of int * int * TempVariableType
        | TempIntType of Set<int>

    module private TempVariableType = 
        let rec unfoldTempVariableType (x : Identifier) (t : TempVariableType) = 
            match t with 
            | TempBoolType -> (x, BoolType) |> List.singleton
            | TempArrayType(l, h, t) -> 
                [l..h]
                |> List.map (fun i -> 
                    unfoldTempVariableType (x + "[" + string(i) + "]") t
                    )
                |> List.concat
            | TempIntType l -> (x, IntType l) |> List.singleton


    let private typeDeclarationParser = 
        let varTypeParser, varTypeParserRef = createParserForwardedToRef()

        let tempIntTypeAsRanegParser = 
            // We treate the type a..b as a shorthand for {a, a+1, ..., b}
            pint32 .>> pstring ".." .>>. pint32
            |>> (fun (x, y) -> [x..y] |> set |> TempIntType)

        let tempBoolTypeParser = 
            stringReturn "boolean" TempBoolType

        let tempIntTypeParser = 
            between (skipChar '{' .>> ws) (skipChar '}') (sepBy (pint32 .>> ws) (skipChar ',' .>> ws))
            |>> fun x -> TempIntType (set x)

        let tempArrayTypeParser = 
            tuple3
                (skipString "array" >>. ws >>. pint32)
                (ws >>. skipString ".." >>. ws >>. pint32)
                (ws >>. skipString "of" >>. ws >>. varTypeParser)
            |>> TempArrayType

        do 
            varTypeParserRef.Value <-
                ws >>. choice [ 
                    tempIntTypeAsRanegParser
                    tempIntTypeParser
                    tempBoolTypeParser
                    tempIntTypeParser
                    tempArrayTypeParser
                ] .>> ws

        pipe2 
            identifierParser 
            (ws >>. pchar ':' >>. ws >>. varTypeParser  .>> ws .>> pchar ';')
            (fun x t -> TempVariableType.unfoldTempVariableType x t)


    let private initParser = 
        pipe2 
            (pstring "init(" >>. ws >>. identifierParser .>> ws .>> pchar ')')
            (ws >>. pstring ":=" >>. ws >>. expParser .>> ws .>> pchar ';')
            (fun x e -> Init(x, e))

    let private nextParser = 
        pipe2
            (pstring "next(" >>. ws >>. identifierParser .>> ws .>> pchar ')')
            (ws >>. pstring ":=" >>. ws >>. expParser .>> ws .>> pchar ';')
            (fun x e -> Next(x, e))

    let private defineParser = 
        pipe2 
            identifierParser 
            (ws >>. pstring ":=" >>. ws >>. expParser .>> ws .>> pchar ';')
            (fun x e -> Define(x, e))

    let private varSectionParser = 
        skipString "VAR" >>. ws >>. many (typeDeclarationParser .>> ws)
        |>> List.concat

    let private assignSectionParser = 
        skipString "ASSIGN" >>. ws >>. many1 (initParser <|> nextParser .>> ws)

    let private defineSectionParser = 
        skipString "DEFINE" >>. ws >>. many (defineParser .>> ws)


    let private bodyParser = 
        many (assignSectionParser <|> defineSectionParser .>> ws)
        |>> (fun x -> 
            let all = List.concat x 

            let inits = 
                all 
                |> List.choose (fun y -> match y with Init (z, e) -> Some (z, e) | _ -> None)

            let nexts = 
                all 
                |> List.choose (fun y -> match y with Next (z, e) -> Some (z, e) | _ -> None)

            let defines = 
                all 
                |> List.choose (fun y -> match y with Define (z, e) -> Some (z, e) | _ -> None)

            inits, nexts, defines
            )

    let private symbolicSystemParser = 
        pipe3
            (ws >>. skipString "MODULE" >>. ws >>. (many1 letter))
            (ws >>. varSectionParser)
            (ws >>. bodyParser)
            (fun _ varTypes (inits, nexts, defines) ->   
               
                {
                    VarTypes = varTypes
                    Init = inits
                    Next = nexts
                    Define = defines
                }
                )
        
    let parseSymbolicSystem (s : String) = 
        let full =
            symbolicSystemParser .>> spaces .>> eof

        let res = run full s

        match res with
        | Success (res, _, _) -> Result.Ok res
        | Failure (err, _, _) -> Result.Error err