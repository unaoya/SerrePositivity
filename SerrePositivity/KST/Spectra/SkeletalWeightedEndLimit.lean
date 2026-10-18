module

public import SerrePositivity.KST.Spectra.SkeletalWeightColimit
public import SerrePositivity.KST.Spectra.PointedWeightedEndWeightLimits

/-!
概要：重み付き end は有限骨格の end の塔の厳密な極限である。
方針：骨格の重みの余極限を反対圏へ移し、end の極限保存を使う。
規約：通常の極限。塔のホモトピー群の極限や ∞ 圏の極限とはまだ比較しない。
使われ方：Goerss–Jardine VIII §1。Tot と部分 Tot の塔の復元の基礎。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.SkeletalWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 概要：全体の end から有限骨格の end への標準錐は極限錐。
方針：骨格の余極限の反対錐を重みに反変な end 関手で移す。
規約：Kan 性を仮定しない厳密な極限の主張。
使われ方：Goerss–Jardine VIII §1。全体の Tot の塔からの復元。 -/
def coneIsLimit (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) :
    IsLimit (cone W D) :=
  isLimitOfPreserves (PointedWeightedEnd.weightFunctor D) (weightCoconeIsColimit W).op

/-- 概要：全体の重み付き end と骨格の end の塔の極限の標準同型。
方針：標準錐の極限性と選択された極限の一意性を使う。
規約：同型の順射は有限骨格への実際の制限族。
使われ方：Goerss–Jardine VIII §1。塔の解析結果を全体の Tot へ戻す界面。 -/
def limitIso (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) :
    PointedWeightedEnd.obj W D ≅ limit (tower W D) :=
  (coneIsLimit W D).conePointUniqueUpToIso (limit.isLimit (tower W D))

@[reassoc]
lemma limitIso_π (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) (n : ℕᵒᵖ) :
    (limitIso W D).hom ≫ limit.π (tower W D) n =
      PointedWeightedEnd.preMap (weightInclusion W n.unop) D :=
  (coneIsLimit W D).conePointUniqueUpToIso_hom_comp (limit.isLimit (tower W D)) n

end

end SerrePositivity.KST.Spectra.SkeletalWeightedEnd
