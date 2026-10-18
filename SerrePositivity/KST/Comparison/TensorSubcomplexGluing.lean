module

public import SerrePositivity.KST.Comparison.SubcomplexUnionCocone
public import SerrePositivity.KST.Comparison.CoconeBaseGluing
public import SerrePositivity.KST.Comparison.CartesianTensorSquare

/-!
# 部分単体集合の和でのホモトピー引き戻しの貼り合わせ

概要：固定因子の写像を持つ四角形を、二つの部分単体集合と交叉からその和へ貼り合わせる。
方針：積を取った部分対象の pushout と、固定射へのファイバーの貼り合わせを使う。
規約：Segal 1974 Proposition 1.6 の標準単体の境界の有限被覆。
使われ方：面とその有限交叉から境界全体の四角形を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory Functor
variable {X' X K T' T : SSet.{u}} {f : X' ⟶ X}
    {a : X' ⊗ K ⟶ T'} {p : T' ⟶ T} {b : X ⊗ K ⟶ T}

/--
概要：固定因子の写像を持つ四角形を、右因子の部分単体集合へ制限する。
方針：独立した二因子の作用の厳密な引き戻しと横に合成する。
規約：元の四角形のホモトピー引き戻し性はここでは要求しない。
使われ方：部分対象ごとの性質を述べる。
-/
theorem tensorSubcomplexSquare (sq : CommSq a (f ▷ K) p b) (U : K.Subcomplex) :
    CommSq ((X' ◁ U.ι) ≫ a) (f ▷ (U : SSet.{u})) p ((X ◁ U.ι) ≫ b) :=
  (cartesianTensorSquare_isPullback f U.ι).toCommSq.horiz_comp sq

/--
概要：二つの部分単体集合とその交叉で成り立つホモトピー引き戻し性は、その和でも成り立つ。
方針：積を取った交叉・和の余錐へ、固定射へのファイバーの貼り合わせを適用する。
規約：部分対象や固定因子の Kan 性は要求しない。
使われ方：標準単体の境界の有限被覆の帰納。
-/
theorem tensorSubcomplex_homotopyPullback_sup (sq : CommSq a (f ▷ K) p b)
    (U V : K.Subcomplex)
    (hU : IsHomotopyPullback (tensorSubcomplexSquare sq U))
    (hV : IsHomotopyPullback (tensorSubcomplexSquare sq V))
    (hI : IsHomotopyPullback (tensorSubcomplexSquare sq (U ⊓ V))) :
    IsHomotopyPullback (tensorSubcomplexSquare sq (U ⊔ V)) := by
  let S := subcomplexUnionSpan U V
  let cA := tensorSubcomplexUnionCocone X' U V
  let cY := tensorSubcomplexUnionCocone X U V
  let β := whiskerLeft S ((tensoringLeft SSet.{u}).map f)
  let : Mono ((subcomplexUnionSpan U V ⋙ tensorLeft X').map WalkingSpan.Hom.snd) :=
    tensorLeft_mono_of_mono X' (SSet.Subcomplex.homOfLE (inf_le_right : U ⊓ V ≤ V))
  let : Mono ((subcomplexUnionSpan U V ⋙ tensorLeft X).map WalkingSpan.Hom.snd) :=
    tensorLeft_mono_of_mono X (SSet.Subcomplex.homOfLE (inf_le_right : U ⊓ V ≤ V))
  have hb d : cA.ι.app d ≫ (f ▷ (U ⊔ V : K.Subcomplex).toSSet) = β.app d ≫ cY.ι.app d :=
    ((tensoringLeft SSet.{u}).map f).naturality ((subcomplexUnionCocone U V).ι.app d)
  apply coconeBase_homotopyPullback_of_span cA (tensorSubcomplexUnionCoconeIsColimit X' U V)
    cY (tensorSubcomplexUnionCoconeIsColimit X U V) β (f ▷ (U ⊔ V : K.Subcomplex).toSSet) hb
    (tensorSubcomplexSquare sq (U ⊔ V))
  rintro (_ | _ | _)
  · exact hI
  · exact hU
  · exact hV

end SerrePositivity.KST.Comparison
