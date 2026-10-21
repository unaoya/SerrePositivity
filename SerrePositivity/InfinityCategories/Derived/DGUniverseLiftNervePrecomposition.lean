module
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLiftInputComposition
/-!
概要：共通対象宇宙の入力持ち上げの前合成・合成等式を、元の nerve の厳密等式にする。
方針：既存の dg 関手等式に nerve を適用し、同じ二段合成を展開する。
規約：元の入力写像を保持する。使われ方：unlifted 分解比較の前合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A B C : Type (max (u + 1) v w))
  [DGCategory R A] [DGCategory R B] [DGCategory R C]
omit [DGCategory R C] in
/-- 元の入力 Up と持ち上げた入力の合成は、元の入力 nerve と次の Up の合成に一致する。 -/
lemma dgUniverseLift_sourcePrecomp_nerve (H : DGFunctor R A B) :
    dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A) ≫
      dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
        (H.comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B))) =
      dgNerve.map H ≫
        dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B) := by
  have h := congrArg (fun G => dgNerve.map G)
    (dgUniverseLift_sourcePrecomp.{u, v, w} R A B H)
  simpa only [dgNerve.map_comp] using h
/-- 二つの持ち上げた実入力写像の nerve の合成は、同じ合成入力の持ち上げの nerve。 -/
lemma dgUniverseLift_inputPrecomp_comp_nerve (H : DGFunctor R A B) (J : DGFunctor R B C) :
    dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
      (H.comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B))) ≫
      dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R B).comp
        (J.comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C))) =
      dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
        ((H.comp J).comp
          (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C))) := by
  have h := congrArg (fun G => dgNerve.map G)
    (dgUniverseLift_inputPrecomp_comp.{u, max (u + 1) v w, w} R A B C H J)
  simpa only [dgNerve.map_comp] using h
end SerrePositivity.InfinityCategories
