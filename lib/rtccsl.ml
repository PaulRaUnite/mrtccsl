type 'a interval = 'a * 'a

type ('c, 't) constr =
  | Precedence of 'c * 'c
  | Causality of 'c * 'c
  | Exclusion of 'c list
  | Coincidence of 'c list
  | Subclocking of 'c * 'c
  | Minus of 'c * 'c * 'c list
  | Delay of 'c * 'c * (int*int) * 'c option
  | Fastest of 'c * 'c list
  | Slowest of 'c * 'c list
  | Intersection of 'c * 'c list
  | Union of 'c * 'c list
  | Periodic of 'c * 'c * int
  | Sample of 'c * 'c * 'c
  | Alternate of 'c * 'c
  | RTdelay of 'c * 'c * 't interval
  | CumulPeriodic of 'c * 't * 't interval * 't
  | AbsPeriodic of 'c * 't * 't interval * 't
  | FirstSampled of 'c * 'c * 'c
  | LastSampled of 'c * 'c * 'c
  | Forbid of 'c * 'c * 'c list
  | Allow of 'c * 'c * 'c list
  | Sporadic of 'c * 't

type ('c, 't) specification = ('c, 't) constr list
