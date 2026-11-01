module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Zigzag

/-!
# 元の頂点と全列による zigzag の等式

概要：全頂点の等式と全列の異種等式から、元の zigzag の等式を得る。
方針：頂点の族を同定した後、列の族を同定する。
規約：端点と射の類の証明は命題であり、元の列のデータを変更しない。
使われ方：語の恒等・合成の作用の全対象での照合。
-/

@[expose] public section
universe u v

namespace SerrePositivity.EInfinity.Hammock.Zigzag
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : Word} {X Y : C}

/-- 全頂点と元の全列は、固定端点の zigzag を一意に決める。 -/
lemma object_ext (S T : Zigzag W w X Y) (hv : ∀ i, S.vertex i = T.vertex i)
    (ha : ∀ i, HEq (S.arrow i) (T.arrow i)) : S = T := by
  cases S
  cases T
  have h := funext hv
  cases h
  have h := funext (fun i => eq_of_heq (ha i))
  cases h
  rfl

/-- 対象の等式と全成分の異種等式による、元の縦射の異種等式。 -/
lemma hom_hext {S T S' T' : Zigzag W w X Y} (hS : S = S') (hT : T = T')
    (f : Hom S T) (g : Hom S' T') (ha : ∀ i, HEq (f.app i) (g.app i)) : HEq f g := by
  cases hS
  cases hT
  exact heq_of_eq (hom_ext f g (fun i => eq_of_heq (ha i)))

/-- 同じ元の縦射の成分は、頂点の等式に沿って異種等しい。 -/
lemma app_heq {S T : Zigzag W w X Y} (f : Hom S T) {i j : Fin (w.length + 1)}
    (hij : i = j) : HEq (f.app i) (f.app j) := by
  cases hij
  rfl

end SerrePositivity.EInfinity.Hammock.Zigzag
