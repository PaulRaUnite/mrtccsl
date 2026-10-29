open Mrtccsl
open Common
open Prelude

module NaiveBackend = struct
  let test_name = "naive"

  module N = Number.Integer

  module Backend = struct
    include Backend.Naive.Make (String) (N)

    type repr = accept

    let of_spec = accept_of_spec
  end

  module Trace = struct
    include Trace.MakeIO (N) (Backend.L)

    type t = trace
  end
end

include Correctness.Make (NaiveBackend)
