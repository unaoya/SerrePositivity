module
public import SerrePositivity.KST.SConstruction.SerreCubeTopGeneratorIndex

/-! # 元の一端点標準面の tensor 生成元添字
概要：指定座標だけを端点にし、他を全て辺とする元の tensor 生成元を指定する。
方針：元の右端からの面座標に従い、右端挿入と辺保持を再帰する。
規約：元の端点番号と右端座標を保持。使われ方：元の全面境界の HA 値への移送。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の座標 i だけを端点 b にし、他の元の座標を辺にした tensor 添字。 -/
def serreCubeFaceGeneratorIndex (b : Bool) : (n : ℕ) → Fin (n + 1) →
    SerreCubeGeneratorIndex (n + 1)
  | 0, _ => (serreCubeTopGeneratorIndex 0, serreCubeGeneratorEndpointIndex b)
  | n + 1, i => Fin.cases
      (serreCubeTopGeneratorIndex (n + 1), serreCubeGeneratorEndpointIndex b)
      (fun j => (serreCubeFaceGeneratorIndex b n j, 2)) i

/-- 元の右端面の添字は、元の全辺添字への同じ端点の付加。 -/
lemma serreCubeFaceGeneratorIndex_zero (b : Bool) (n : ℕ) :
    serreCubeFaceGeneratorIndex b n 0 =
      (serreCubeTopGeneratorIndex n, serreCubeGeneratorEndpointIndex b) := by
  cases n <;> rfl

/-- 元の内側面の添字は、一段小さい同じ面添字への元の辺の付加。 -/
lemma serreCubeFaceGeneratorIndex_succ (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    serreCubeFaceGeneratorIndex b (n + 1) i.succ = (serreCubeFaceGeneratorIndex b n i, 2) := rfl

/-- 元の一端点面添字の自由次元は、元の面の始域次元。 -/
lemma serreCubeFaceGeneratorIndex_freeDimension (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    serreCubeGeneratorFreeDimension (n + 1) (serreCubeFaceGeneratorIndex b n i) = n := by
  induction n with
  | zero => cases b <;> rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b <;> exact serreCubeTopGeneratorIndex_freeDimension (n + 1)
    · exact congrArg (· + 1) (ih j)

/-- 元の一端点面添字の次数は、元の面の始域次元の負値。 -/
lemma serreCubeFaceGeneratorIndex_degree (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    serreCubeGeneratorDegree (n + 1) (serreCubeFaceGeneratorIndex b n i) = -(n : ℤ) :=
  (serreCubeGeneratorDegree_freeDimension (n + 1) (serreCubeFaceGeneratorIndex b n i)).trans
    (congrArg (fun d : ℕ => -(d : ℤ)) (serreCubeFaceGeneratorIndex_freeDimension b n i))

end SerrePositivity.KST.SConstruction
