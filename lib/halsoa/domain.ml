(*TODO: prbably move to rtccsl itself*)
type 'n distribution =
  | Uniform of
      { lower : 'n
      ; upper : 'n
      }
  | TrunkNormal of
      { mean : 'n
      ; dev : 'n
      ; lower : 'n
      ; upper : 'n
      }
[@@deriving map]

type 'n trig_policy =
  | Timer of 'n distribution
  | Event of string
[@@deriving map]

type 'n service =
  { inputs : string list
  ; outputs : string list
  ; execution_time : 'n distribution
  ; trigger : 'n trig_policy
  }
[@@deriving map]

type 'n component = 'n service list
[@@deriving map]

type 'n signal =
  | Sensor of
      { name : string
      ; period : 'n distribution
      ; latency : 'n distribution
      }
  | Actuator of
      { name : string
      ; period : 'n distribution
      ; latency : 'n distribution
      }
[@@deriving map]

type 'n hal = 'n signal list
[@@deriving map]
type 'n system = 'n component list * 'n hal
[@@deriving map]


