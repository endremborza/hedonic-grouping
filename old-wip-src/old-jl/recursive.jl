### base

mutable struct Agent
    id::Any
    current_allocation::Set

end


Base.hash(a::Agent) = hash(a.id)
Base.isequal(a1::Agent, a2::Agent) = a1.id == a2.id


struct Problem
    outproposals::Dict
    inproposals::Dict

end


function eliminate(problem, sets)
    for trash in sets
        for a in trash
            problem["prefs"][a].remove(trash)
            if trash in problem["out_proposals"][a]
                problem["out_proposals"][a].remove(trash)
            end
            for prop in problem["in_proposals"][a]
                if prop["what"]==trash
                    problem["in_proposals"][a].remove(prop)
                end
            end
        end
    end
    return problem
end

Set([1,2]) |> length


function recurse(problem, J)
    finished = false
    problem["forced_moves"].append(J)

    while !finished
        finished = true
        for a in agents
            has_proposed = set(problem["out_proposals"][a]).difference(set(problem["forced_moves"]))
            if has_proposed |> isempty
                continue
            end
            finished = false
            applicable_prefs = [x for x in problem["prefs"][a] if !(x in problem["out_proposals"][a])]
            if applicable_prefs |> isempty
                return "UNSTABLE"  # SOMEONE RAN OUT - CANT MOVE ON
            end
            H = applicable_prefs[0]
            problem["out_proposals"][a].append(H)
            for b in setdiff(H,Set([a]))
                if problem["in_proposals"][b] |> isempty #NOT RECEIVED ANY OFFER YET
                    problem["in_proposals"][b].append({"from":set([a]),"what":H})
                    if (len(H)==2) #CONSIDERED (OTHERS REJECTED)
                        offer_pref = problem["prefs"][b].index(H)
                        to_eliminate = [s for s in problem["prefs"][b][offer_pref+1:end]]
                        problem = eliminate(problem,to_eliminate)
                    end
                else
                    already_in = "NA"
                    for i in range(0,len(problem["in_proposals"][b]))
                        held = problem["in_proposals"][b][i]
                        if held["what"]==H
                            already_in = i
                        end
                    end
                    if already_in == "NA" #NOT RECEIVED SUCH OFFER YET
                        problem["in_proposals"][b].append({"from":set([a]),"what":H})
                        became_cons = (len(H)==2)
                    else
                        problem["in_proposals"][b][already_in]["from"] = problem["in_proposals"][b][already_in]["from"].union(set([a]))
                        became_cons = (len(problem["in_proposals"][b][already_in]["from"]) == len(H)-1)
                    if became_cons == True #CONSIDERED (OTHERS REJECTED)
                        offer_pref = problem["prefs"][b].index(H)
                        to_eliminate = [s for s in problem["prefs"][b][offer_pref+1:end]]
                        problem = eliminate(problem,to_eliminate)
                    end
                end
            end
        end
        if finished
            for a in problem["agents"]
                applicable_prefs = [x for x in problem["prefs"][a] if !(x in problem["out_proposals"][a])]
                if len(applicable_prefs)>0
                    finished = false
                    K = problem["out_proposals"][a][-1]
                    probing = copy.deepcopy(problem)
                    answer = recurse(probing, K)
                    if answer == "UNSTABLE"
                        problem = eliminate(problem, applicable_prefs)
                        break
                    else
                        problem = answer
                        break
                    end
                end
            end
        end
    end
    return problem
end


