type fattreeCut =
  | Vertical
  | Horizontal
  | Pods
  | Spines
  | Full

type fattreeNode =
  | Core
  | Aggregation
  | Edge

type networkCut = { cut : fattreeCut }

let partition decls cut = decls
