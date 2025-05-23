open Prelude
open Mrtccsl.Automata.Simple

type 'n bounded_distribution =
  { bounds : 'n * 'n
  ; dist : 'n distribution
  }
[@@deriving map]

type id = string

type 'n trig_policy =
  [ `AbsoluteTimer of 'n * 'n bounded_distribution
  | `CumulativeTimer of 'n bounded_distribution
  | `Signal of id
  ]
[@@deriving map]

type 'n service =
  { name : id
  ; inputs : id list
  ; outputs : id list
  ; execution_time : 'n bounded_distribution
  ; policy : 'n trig_policy
    (*TODO: add ability to specify the dependencies between inputs and outputs*)
  }
[@@deriving map]

type 'n component =
  { name : id
  ; services : 'n service list
  }
[@@deriving map]

type 'n signal =
  | Sensor of
      { as_device : bool
      ; policy :
          [ `AbsoluteTimer of 'n * 'n bounded_distribution
          | `CumulativeTimer of 'n bounded_distribution
          ]
      ; latency : 'n bounded_distribution
      }
  | Actuator of
      { policy : 'n trig_policy
      ; latency : 'n bounded_distribution
      }
[@@deriving map]

type 'n hal = (id, 'n signal) Hashtbl.t [@@deriving map]
type 'n system = 'n component list * 'n hal [@@deriving map]
