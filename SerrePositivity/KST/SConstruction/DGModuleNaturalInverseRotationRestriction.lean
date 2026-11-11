module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalInverseRotationBoundary

/-!
概要：元全実逆回転の指定包含制限を同じ元負符号へ回収する。
方針：元三因子の閉成分と同じ実 shift の合成保存を使う。
規約：元全比較と指定相殺を保持する。
使われ方：実逆回転を含む指定上二単体の長辺。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma restrictTriple {C D : Type*} [Category C] [Category D]
    (Q : C ⥤ D) {A B C' : C} {X Z : D}
    (a : A ⟶ B) (b : B ⟶ C') (j : Q.obj A ⟶ X)
    (e : X ⟶ Q.obj B) (c : Q.obj C' ⟶ Z) (h : j ≫ e = Q.map a) :
    j ≫ ((e ≫ Q.map b) ≫ c) = Q.map (a ≫ b) ≫ c := by
  rw [← Category.assoc, ← Category.assoc, h, ← Q.map_comp]
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "GS" => G.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "CD" => dgModuleNaturalConeFunctor R D (CF) (FS) (δ)
local notation "S" => moduleShiftDG R D (-1)
local notation "L" => dgModuleNaturalInverseRotationSource R D F G η
local notation "α" => dgModuleNaturalInverseRotationConeShift R D F G η
local notation "β" => dgModuleNaturalInverseRotationShiftedComparison R D F G η
local notation "γ" => dgModuleNaturalInverseRotationCancellation R D G
local notation "ν" => dgModuleNaturalConeInr R D (CF) (FS) (δ)


local notation "b" => dgModuleNaturalConeArrow R D (CD) (GS)
  (dgModuleNaturalConnectingConeComposite R D F G η)
local notation "k" => fun x : P => Iso.hom (dgModuleSpecifiedCancellationIso R D (G.obj x))

/-- 概要：元全実逆回転の閉射は同じ三つの元閉成分の合成。
方針：全厳密合成と元実 shift・指定相殺の閉射回収を使用する。
規約：同じ元因子。使われ方：指定包含制限の計算。 -/
lemma dgModuleNaturalInverseRotation_arrow_factors (x : P) :
    dgModuleNaturalConeArrow R D (L) G (dgModuleNaturalInverseRotation R D F G η) x =
      (dgModuleNaturalConeArrow R D (L) ((CD).comp (S)) (α) x ≫
        moduleShiftMap R D (-1) (b x)) ≫ k x := by
  exact (dgModuleNaturalConeArrow_comp R D (L) ((GS).comp (S)) G
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (α) (β)) (γ) x).trans
      (congrArg₂ (fun p q => p ≫ q)
        ((dgModuleNaturalConeArrow_comp R D (L) ((CD).comp (S)) ((GS).comp (S))
          (α) (β) x).trans
            (congrArg (fun q => dgModuleNaturalConeArrow R D (L) ((CD).comp (S)) (α) x ≫ q)
              (dgModuleNaturalConeShiftArrow R D (CD) (GS)
                (dgModuleNaturalConnectingConeComposite R D F G η) (-1) x)))
        ((dgModuleNaturalInverseRotationCancellation_arrow R D G x).trans
          (dgModuleSpecifiedCancellationStrictComparison_arrow R D (G.obj x))))

/-- 概要：元全実逆回転の右包含制限は元 connecting 制限の実逆 shift。
方針：cone shift の包含回収と同じ shift の合成保存を使用する。
規約：指定相殺を保持。使われ方：元上二単体の長辺回収。 -/
lemma dgModuleNaturalInverseRotation_inr (x : P) :
    moduleConeInr R D
      (dgModuleNaturalConeArrow R D ((CF).comp (S)) ((FS).comp (S))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (δ) (S)) x) ≫
      dgModuleNaturalConeArrow R D (L) G (dgModuleNaturalInverseRotation R D F G η) x =
        moduleShiftMap R D (-1)
          (moduleConeInr R D (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x) ≫ b x) ≫ k x := by
  rw [dgModuleNaturalInverseRotation_arrow_factors]
  exact restrictTriple (moduleShiftFunctor R D (-1)) _ _ _ _ _
    (dgModuleNaturalInverseRotationConeShift_inr R D F G η x)

/-- 概要：元比較の shift の負を同じ全族の二端点で保持する。
方針：元の登録 shift 射を明示した実端点で保持する。
規約：負符号を変更しない。使われ方：逆 shift 制限の長辺。 -/
def dgModuleNaturalInverseRotationSignedArrow (x : P) :
    ForgetEnrichment.of (Complex R) ((FS).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((GS).obj x) :=
  -(dgModuleNaturalConeArrow R D F G η x)⟦(1 : ℤ)⟧'

/-- 概要：元全実逆回転の右包含制限は元比較の shift 負符号を保持する。
方針：元 connecting 全比較の同じ指定符号を逆 shift へ写す。
規約：同じ負符号・同じ指定相殺。使われ方：実上二単体の指定合成辺。 -/
lemma dgModuleNaturalInverseRotation_inr_sign (x : P) :
    moduleConeInr R D
      (dgModuleNaturalConeArrow R D ((CF).comp (S)) ((FS).comp (S))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (δ) (S)) x) ≫
      dgModuleNaturalConeArrow R D (L) G (dgModuleNaturalInverseRotation R D F G η) x =
        moduleShiftMap R D (-1)
          (dgModuleNaturalInverseRotationSignedArrow R D F G η x) ≫ k x :=
  (dgModuleNaturalInverseRotation_inr R D F G η x).trans
    (congrArg (fun t => moduleShiftMap R D (-1) t ≫ k x)
      (dgModuleNaturalConnectingConeComposite_inr_sign R D F G η x))
end SerrePositivity.KST.SConstruction
