let reaction_name dir chain_name span =
  let start, finish = span in
  Printf.sprintf "%s/%s/%s_%s.reaction.csv" dir chain_name start finish
;;

let histogram_name dir chain_name span =
  let start, finish = span in
  Printf.sprintf "%s/%s/%s_%s.histogram.csv" dir chain_name start finish
;;
