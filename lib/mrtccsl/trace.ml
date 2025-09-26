module type Container = sig
  type 'a t
end

module type Element = sig end

module type Label = sig
  module E : Element

  type t
end

module type Timestamp = sig
  type t
end

module Make (C : Container) (L : Label) (T : Timestamp) = struct
  type t = L.t C.t

  module Export = struct end
  module Import = struct end
end
