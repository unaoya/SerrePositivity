module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullColimitReflection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullPullbackReflection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberPushout

/-! # 充満 dg 部分圏内の標準 cofiber 四角形

概要：A,B,C と標準 cofiber が部分圏に属せば、標準 cofiber 四角形は部分圏内の ∞ 押し出しになる。
方針：二つの標準三角形を部分圏へ持ち上げて貼り、周囲の押し出し性を反映する。
規約：HTT §1.2.13、HA §1.3.1。使われ方：cofiber で閉じた部分圏、特に Semifree への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial

variable {S : Type u} [CommRing S] (P : Complex S → Prop) {A B C : Complex S}

/-- 充満部分圏の四角形の包含像が押し出しなら元の四角形も押し出し。 -/
lemma isPushoutSquare_of_fullInclusion
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (DGFullSubcategory (Complex S) P))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion S (Complex S) P))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isColimitCone_of_fullInclusion S (Complex S) P (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)
  exact hF

/-- 概要：P 内の標準 cofiber の上三角形を部分圏の単体へ持ち上げる。
方針：三頂点 A,C,Q にそれぞれの所属の証明を添え、Hom 成分は変えない。
規約：HA Construction 1.3.1.6。使われ方：部分圏の標準四角形の第一セル。 -/
def fullCofiberUpperTriangle (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hC : P C) (hP : P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (DGFullSubcategory (Complex S) P) 2 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull S (Complex S) P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberUpperTriangle f g).simplex (fun i => by
    fin_cases i
    · exact hA
    · exact hC
    · exact hP)

/-- 概要：P 内の標準 cofiber の下三角形を部分圏の単体へ持ち上げる。
方針：三頂点 A,B,Q にそれぞれの所属の証明を添え、Hom 成分は変えない。
規約：HA Construction 1.3.1.6。使われ方：部分圏の標準四角形の第二セル。 -/
def fullCofiberLowerTriangle (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hP : P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (DGFullSubcategory (Complex S) P) 2 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull S (Complex S) P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberLowerTriangle f g).simplex (fun i => by
    fin_cases i
    · exact hA
    · exact hB
    · exact hP)

/-- 概要：部分圏へ持ち上げた標準の二三角形は対角で一致する。
方針：包含の単射性で周囲へ戻し、標準三角形の対角の式を使う。
規約：HTT §1.2.13。使われ方：部分圏内の四角形の貼合せ。 -/
lemma fullCofiberTriangles_compatible (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g)) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫
        (SSet.yonedaEquiv.symm (fullCofiberUpperTriangle P f g hA hC hP) :
          (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (DGFullSubcategory (Complex S) P)) =
      SSet.stdSimplex.δ (1 : Fin 3) ≫
        SSet.yonedaEquiv.symm (fullCofiberLowerTriangle P f g hA hB hP) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion S (Complex S) P))).1
  simp only [Category.assoc, fullCofiberUpperTriangle, fullCofiberLowerTriangle,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull_yoneda_inclusion]
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberUpperTriangle f g).d₁, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberLowerTriangle f g).d₁]

/-- 概要：標準 cofiber の四頂点が P を満たすと、四角形を充満部分圏内に構成できる。
方針：上・下三角形を部分圏へ持ち上げ、対角に沿った押し出しで貼る。
規約：HTT §1.2.13。使われ方：閉性の定理から部分圏の押し出しを作る。 -/
def fullCofiberSquare (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g)) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (DGFullSubcategory (Complex S) P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (SSet.yonedaEquiv.symm (fullCofiberUpperTriangle P f g hA hC hP))
    (SSet.yonedaEquiv.symm (fullCofiberLowerTriangle P f g hA hB hP))
    (fullCofiberTriangles_compatible P f g hA hB hC hP)

/-- 概要：部分圏内の標準四角形の包含像は周囲の標準 cofiber 四角形に等しい。
方針：二三角形の押し出しによる外延性と liftToFull の包含像の公式を使う。
規約：HTT §1.2.13。使われ方：周囲の押し出し性を部分圏へ戻す。 -/
lemma fullCofiberSquare_inclusion (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g)) :
    fullCofiberSquare P f g hA hB hC hP ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion S (Complex S) P) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [← Category.assoc]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc _ _ _) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare_upper]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull_yoneda_inclusion S (Complex S) P _ _
  · rw [← Category.assoc]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc _ _ _) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare_lower]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull_yoneda_inclusion S (Complex S) P _ _

/-- 概要：cofiber が部分圏に属する標準 cofiber 四角形は部分圏の dg nerve の ∞ 押し出し。
方針：包含像を周囲の標準四角形に同定し、本レーンの押し出し性を充満部分圏へ反映する。
規約：HTT §1.2.13。使われ方：cofiber と有限直和で閉じた部分圏、特に Semifree の押し出し。 -/
lemma fullCofiberSquare_isPushout (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (fullCofiberSquare P f g hA hB hC hP) := by
  apply isPushoutSquare_of_fullInclusion P
  rw [fullCofiberSquare_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare_isPushout f g

end SerrePositivity.InfinityCategories.Project.DerivedCategories
