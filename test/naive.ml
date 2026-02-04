
open Mrtccsl
open Prelude

module NaiveBackend = struct
  let test_name = "naive"

  module N = Number.Integer
  module Backend = Backend.Naive.Make (String) (N)

  module Trace = struct
    include Trace.MakeIO (N) (Backend.L)

    type t = trace
  end
end

include Correctness.Make (NaiveBackend)