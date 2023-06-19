module TransitionSystemLib.TransitionSystem

open Util 

open System
open System.IO
open System.Collections.Generic

type TransitionSystem<'L when 'L : comparison> = 
    {
        States : Set<int>
        InitialStates : Set<int>
        APs : list<'L>
        Edges : Map<int, Set<int>>
        ApEval : Map<int, Set<int>>
    }

module TransitionSystem =

    let mapAPs (f : 'L -> 'U) (ts : TransitionSystem<'L>) = 
        {
            States = ts.States
            InitialStates = ts.InitialStates
            APs = ts.APs |> List.map f
            Edges = ts.Edges
            ApEval = ts.ApEval
        }

    exception private NotWellFormedException of String

    let findError (ts : TransitionSystem<'L>) =
        try 
            ts.States
            |> Seq.iter (fun x -> 
                if ts.Edges.ContainsKey x |> not then 
                    raise <| NotWellFormedException $"No successor defined for state $i{x}"

                if ts.ApEval.ContainsKey x |> not then 
                    raise <| NotWellFormedException $"No AP-Eval defined for state $i{x}"
                    
                ts.ApEval.[x]
                |> Set.iter (fun i ->
                    if i < 0 || i >= ts.APs.Length then
                        raise <| NotWellFormedException $"The AP-Eval for state $i{x} uses index %i{i} which is out of range of the used APs"
                    )
                ) 

            ts.InitialStates
            |> Seq.iter (fun s -> 
                if ts.States.Contains s |> not then 
                    raise <| NotWellFormedException $"The initial state is not contained in the set of all states"
                )
            
            ts.Edges
            |> Map.toSeq
            |> Seq.iter (fun (k, x) ->
                x
                |> Seq.iter (fun z -> 
                    if ts.States.Contains z |> not then 
                        raise <| NotWellFormedException $"State $i{z} is a successor of states %i{k} but not defined as a state"
                )
            )

            None 
        with 
        | NotWellFormedException msg -> Some msg
      
    let print (stringerAp : 'L -> string) (ts : TransitionSystem<'L>) = 

        let strWriter = new StringWriter()
       
        strWriter.Write("aps ")
        for x in ts.APs do 
            strWriter.Write("\"" + stringerAp(x) + "\"" + " ")
        strWriter.Write('\n')

        strWriter.Write("init ")
        for s in ts.InitialStates do
            strWriter.Write(string(s) + " ")
        strWriter.Write('\n')

        strWriter.Write("--BODY--\n")

        for s in ts.States do
            let sucs = ts.Edges.[s]
            let apEval = ts.ApEval.[s]

            strWriter.Write("State: " + string(s) + " ")
            strWriter.Write (
                "{" +
                (apEval
                |> Set.map (fun x -> string x)
                |> Set.toList
                |> Util.combineStringsWithSeperator " ")
                + "}"
                )
            strWriter.Write('\n')

            for x in sucs do 
                strWriter.Write(string(x) + " ")

            strWriter.Write('\n')
        
        strWriter.Write("--END--\n")
        
        strWriter.ToString()


    let computeBisimulationQuotient (ts : TransitionSystem<'L>) = 
        // Helper function to split a part of the partition
        let splitPartition (stateToPartitionId : Map<int,int>) partitionId = 
            let statesInPartitionId = 
                stateToPartitionId
                |> Map.toSeq 
                |> Seq.filter (fun (_, x) -> x = partitionId)
                |> Seq.map fst

            if Seq.length statesInPartitionId <= 1 then 
                // This partition contains only one state, cannot be split further
                None
            else 

                let c = 
                    statesInPartitionId
                    // Map all states to the successor partitions
                    |> Seq.map (fun s -> 
                        let sucPartiations = 
                            ts.Edges.[s]
                            |> Set.map (fun s' -> stateToPartitionId.[s'])
                        sucPartiations, s
                        )
                    |> Seq.groupBy fst 
                    |> Seq.map (fun (k, el) -> k, Seq.map snd el |> set)
                    |> Map.ofSeq

                if Map.count c = 1 then 
                    // All states point to the same set of partitions, no need to split 
                    None 
                else 
                    Map.values c
                    |> seq 
                    |> Some

        // We init the partition based only on the AP evaluation of each state
        let initStateToPartitionId = 
            ts.States 
            |> Seq.groupBy (fun s -> ts.ApEval.[s])
            |> Seq.map snd
            |> Seq.mapi (fun i states ->
                states 
                |> Seq.map (fun s -> s, i)
                )
            |> Seq.concat
            |> Map.ofSeq

        let rec iterativeSplit (stateToPartitionId : Map<int, int>) = 
            let partitionIDs = 
                stateToPartitionId
                |> Map.toSeq 
                |> Seq.map snd 
                |> Seq.distinct

            let mutable freshId = Seq.max partitionIDs + 1

            // Use lazyness here to not do all the work
            partitionIDs
            |> Seq.choose (fun id -> splitPartition stateToPartitionId id)
            |> Seq.tryHead
            |> function 
                | None -> 
                    // We are done, nothing left to split
                    stateToPartitionId
                | Some newPartitions -> 

                    let newSplit = 
                        (stateToPartitionId, newPartitions)
                        ||> Seq.fold (fun m states -> 
                            let newId = freshId
                            freshId <- freshId + 1

                            (m, states)
                            ||> Set.fold (fun mm s -> 
                                // Overwrite the partitionID for s
                                Map.add s newId mm
                                )
                            )

                    iterativeSplit newSplit
        

        let finalStateToPartitionId = iterativeSplit initStateToPartitionId

        let states = Map.values finalStateToPartitionId |> set

        let partiationIdToStates = 
            finalStateToPartitionId
            |> Map.toSeq
            |> Seq.groupBy snd 
            |> Seq.map (fun (k, v) -> k, Seq.map fst v |> set)
            |> Map.ofSeq
                        
        let newTs =
            {
                TransitionSystem.InitialStates = 
                    ts.InitialStates
                    |> Set.map (fun x -> finalStateToPartitionId.[x])
                States = states
                APs = ts.APs
                Edges =
                    states 
                    |> Seq.map (fun id -> 
                        let sucPartitions = 
                            partiationIdToStates.[id]
                            |> Seq.map (fun s -> ts.Edges.[s])
                            |> Seq.concat
                            |> Seq.map (fun s -> finalStateToPartitionId.[s])
                            |> set

                        id, sucPartitions
                        )
                    |> Map.ofSeq

                ApEval = 
                    states 
                    |> Seq.map (fun id -> 
                        let apEval = 
                            finalStateToPartitionId
                            |> Map.toSeq
                            // Find some state in this partition
                            |> Seq.find (fun (_, idd) -> id = idd)
                            |> fun (s, _) -> ts.ApEval.[s]

                        id, apEval
                        )
                    |> Map.ofSeq
            }

        newTs, finalStateToPartitionId
        
module Parser = 
    open FParsec 

    let private apEvalParser =
        between
            (skipChar '{')
            (skipChar '}')
            (spaces >>. many (pint32 .>> spaces))
        |>> set

    let private stateParser = 
        pstring "State:" >>.
            pipe3
                (spaces >>. pint32)
                (spaces >>. apEvalParser)
                (spaces >>. many (pint32 .>> spaces))
                (fun id ap sucs -> (id, (sucs, ap)))

    let private bodyParser = 
        spaces >>. many (stateParser .>> spaces)


    let private transitionSystemParser = 
        pipe3
            (spaces >>. skipString "AP:" >>. spaces >>. many1 (Util.ParserUtil.escapedStringParser .>> spaces))
            (spaces >>. skipString "Init:" >>. spaces >>. many1 (pint32 .>> spaces))
            (spaces >>. skipString "--BODY--" >>. bodyParser .>> spaces .>> skipString "--END--")
            (fun aps init st -> 
                {
                    TransitionSystem.States = st |> List.map fst |> set
                    InitialStates = set init
                    APs = aps;
                    Edges = 
                        st 
                        |> List.map (fun (k, (a, _)) -> k, set a)
                        |> Map.ofList
                    ApEval = 
                        st 
                        |> List.map (fun (k, (_, b)) -> k, b)
                        |> Map.ofList
                }       
                )
    
    let parseTransitionSystem (s: string) =
        let full = transitionSystemParser .>> spaces .>> eof
        let res = run full s
        match res with
            | Success (res, _, _) -> Result.Ok res
            | Failure (err, _, _) -> 
                Result.Error err