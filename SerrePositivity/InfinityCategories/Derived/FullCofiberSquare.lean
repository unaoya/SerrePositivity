module
public import SerrePositivity.InfinityCategories.Derived.FullColimitReflection
public import SerrePositivity.InfinityCategories.DGNerve.FullPullbackReflection
public import SerrePositivity.InfinityCategories.Derived.CofiberPushout

/-! # 充満 dg 部分圏内の標準 cofiber 四角形

概要：A,B,C と標準 cofiber が部分圏に属せば、標準 cofiber 四角形は部分圏内の ∞ 押し出しになる。
方針：二つの標準三角形を部分圏へ持ち上げて貼り、周囲の押し出し性を反映する。
規約：HTT §1.2.13、HA §1.3.1。使われ方：cofiber で閉じた部分圏、特に Semifree への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial

variable {S : Type u} [CommRing S] (P : Complex S → Prop) {A B C : Complex S}

/-- 充満部分圏の四角形の包含像が押し出しなら元の四角形も押し出し。 -/
lemma isPushoutSquare_of_fullInclusion
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve S (DGFullSubcategory (Complex S) P))
    (hF : IsPushoutSquare (F ≫ dgNerve.map (dgFullSubcategoryInclusion S (Complex S) P))) :
    IsPushoutSquare F := by
  apply isColimitCone_of_fullInclusion S (Complex S) P (pushoutCocone F)
  exact hF

/-- 概要：P 内の標準 cofiber の上三角形を部分圏の単体へ持ち上げる。
方針：三頂点 A,C,Q にそれぞれの所属の証明を添え、Hom 成分は変えない。
規約：HA Construction 1.3.1.6。使われ方：部分圏の標準四角形の第一セル。 -/
def fullCofiberUpperTriangle (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hC : P C) (hP : P (pushoutCofiber f g)) :
    Simplex S (DGFullSubcategory (Complex S) P) 2 :=
  liftToFull S (Complex S) P (cofiberUpperTriangle f g).simplex (fun i => by
    fin_cases i
    · exact hA
    · exact hC
    · exact hP)

/-- 概要：P 内の標準 cofiber の下三角形を部分圏の単体へ持ち上げる。
方針：三頂点 A,B,Q にそれぞれの所属の証明を添え、Hom 成分は変えない。
規約：HA Construction 1.3.1.6。使われ方：部分圏の標準四角形の第二セル。 -/
def fullCofiberLowerTriangle (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hP : P (pushoutCofiber f g)) :
    Simplex S (DGFullSubcategory (Complex S) P) 2 :=
  liftToFull S (Complex S) P (cofiberLowerTriangle f g).simplex (fun i => by
    fin_cases i
    · exact hA
    · exact hB
    · exact hP)

/-- 概要：部分圏へ持ち上げた標準の二三角形は対角で一致する。
方針：包含の単射性で周囲へ戻し、標準三角形の対角の式を使う。
規約：HTT §1.2.13。使われ方：部分圏内の四角形の貼合せ。 -/
lemma fullCofiberTriangles_compatible (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (pushoutCofiber f g)) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫
        (SSet.yonedaEquiv.symm (fullCofiberUpperTriangle P f g hA hC hP) :
          (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (DGFullSubcategory (Complex S) P)) =
      SSet.stdSimplex.δ (1 : Fin 3) ≫
        SSet.yonedaEquiv.symm (fullCofiberLowerTriangle P f g hA hB hP) := by
  apply (cancel_mono (dgNerve.map (dgFullSubcategoryInclusion S (Complex S) P))).1
  simp only [Category.assoc, fullCofiberUpperTriangle, fullCofiberLowerTriangle,
    liftToFull_yoneda_inclusion]
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    (cofiberUpperTriangle f g).d₁, (cofiberLowerTriangle f g).d₁]

/-- 概要：標準 cofiber の四頂点が P を満たすと、四角形を充満部分圏内に構成できる。
方針：上・下三角形を部分圏へ持ち上げ、対角に沿った押し出しで貼る。
規約：HTT §1.2.13。使われ方：閉性の定理から部分圏の押し出しを作る。 -/
def fullCofiberSquare (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (pushoutCofiber f g)) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve S (DGFullSubcategory (Complex S) P) :=
  square_isPushout.desc (SSet.yonedaEquiv.symm (fullCofiberUpperTriangle P f g hA hC hP))
    (SSet.yonedaEquiv.symm (fullCofiberLowerTriangle P f g hA hB hP))
    (fullCofiberTriangles_compatible P f g hA hB hC hP)

/-- 概要：部分圏内の標準四角形の包含像は周囲の標準 cofiber 四角形に等しい。
方針：二三角形の押し出しによる外延性と liftToFull の包含像の公式を使う。
規約：HTT §1.2.13。使われ方：周囲の押し出し性を部分圏へ戻す。 -/
lemma fullCofiberSquare_inclusion (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (pushoutCofiber f g)) :
    fullCofiberSquare P f g hA hB hC hP ≫
        dgNerve.map (dgFullSubcategoryInclusion S (Complex S) P) = standardCofiberSquare f g := by
  apply square_isPushout.hom_ext
  · rw [← Category.assoc]
    change (squareTriangle 0 ≫ square_isPushout.desc _ _ _) ≫ _ = _
    rw [square_isPushout.inl_desc, standardCofiberSquare_upper]
    exact liftToFull_yoneda_inclusion S (Complex S) P _ _
  · rw [← Category.assoc]
    change (squareTriangle 1 ≫ square_isPushout.desc _ _ _) ≫ _ = _
    rw [square_isPushout.inr_desc, standardCofiberSquare_lower]
    exact liftToFull_yoneda_inclusion S (Complex S) P _ _

/-- 概要：cofiber が部分圏に属する標準 cofiber 四角形は部分圏の dg nerve の ∞ 押し出し。
方針：包含像を周囲の標準四角形に同定し、N7c の押し出し性を充満部分圏へ反映する。
規約：HTT §1.2.13。使われ方：cofiber と有限直和で閉じた部分圏、特に Semifree の押し出し。 -/
lemma fullCofiberSquare_isPushout (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (pushoutCofiber f g)) :
    IsPushoutSquare (fullCofiberSquare P f g hA hB hC hP) := by
  apply isPushoutSquare_of_fullInclusion P
  rw [fullCofiberSquare_inclusion]
  exact standardCofiberSquare_isPushout f g

end SerrePositivity.InfinityCategories.DGNerve
