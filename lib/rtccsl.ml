type 'a interval = 'a * 'a

type ('c, 't) constr =
  | Precedence of {cause: 'c; effect: 'c}
  | Causality of {cause: 'c; effect: 'c}
  | Exclusion of 'c list
  | Coincidence of 'c list
  | Subclocking of {sub: 'c; super: 'c}
  | Minus of {out: 'c; arg: 'c; except: 'c list}
  | Delay of {out: 'c; arg: 'c; delay: (int*int); base: 'c option}
  | Fastest of {out: 'c; left: 'c; right: 'c}
  | Slowest of {out: 'c; left: 'c; right: 'c}
  | Intersection of {out: 'c ; args: 'c list}
  | Union of {out: 'c ; args: 'c list}
  | Periodic of {out: 'c; base: 'c; period: int}
  | Sample of {out: 'c; arg: 'c; base: 'c}
  | Alternate of {first: 'c; second: 'c}
  | RTdelay of {out: 'c; arg: 'c; delay: 't interval}
  | CumulPeriodic of {out: 'c; period: 't; error: 't interval; offset: 't}
  | AbsPeriodic of {out: 'c; period: 't; error: 't interval; offset: 't }
  | FirstSampled of {out: 'c; arg: 'c; base: 'c}
  | LastSampled of {out: 'c; arg: 'c; base: 'c}
  | Forbid of {from: 'c; until: 'c; args: 'c list}
  | Allow of {from: 'c; until: 'c; args: 'c list}
  | Sporadic of {out: 'c ; at_least: 't; strict: bool}

type ('c, 't) specification = ('c, 't) constr list
