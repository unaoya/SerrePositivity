module

public import Mathlib.CategoryTheory.Monoidal.Category
public import SerrePositivity.DifferentialGraded.Presentation.Category
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHom.CoefficientClosure
public import SerrePositivity.DifferentialGraded.Module.FreeSphereClosedCoefficientCycles
public import SerrePositivity.DifferentialGraded.Module.FreeSphereImageCoefficient
public import SerrePositivity.DifferentialGraded.Functor.CoproductMatrixComparison
public import Mathlib.CategoryTheory.Adjunction.Limits
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.ExtensionRepresentableClosedNaturality

/-!
# Presentation.GeneratedHom.SphereLifts

## 概要
提示の非連結和と自由 sphere・行列・代表加群の同時持ち上げをまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## EnrichedLawTransport（旧 SerrePositivity/DifferentialGraded/Presentation/EnrichedLawTransport.lean） -/

/-!
概要：Hom 対象の等式と単位・合成の異種等式に沿って豊穣圏の三法則を移す。
方針：抽象 Hom 対象上で等式を消去し、実際の提示複体の展開を避ける。
規約：追加の圏法則や公理は仮定せず、元の三法則を入力として移送する。
使われ方：非連結和の提示 Hom の条件分岐を、小さい kernel 項で検証する。
-/

@[expose] public section EnrichedLawTransport
universe u

namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category V] [MonoidalCategory V]

lemma enrichedLeftLaw_of_heq {U H U' H' : V} (hU : U = U') (hH : H = H')
    (i : 𝟙_ V ⟶ U) (i' : 𝟙_ V ⟶ U') (c : U ⊗ H ⟶ H) (c' : U' ⊗ H' ⟶ H')
    (hi : HEq i i') (hc : HEq c c')
    (h : (λ_ H').inv ≫ i' ▷ H' ≫ c' = 𝟙 H') :
    (λ_ H).inv ≫ i ▷ H ≫ c = 𝟙 H := by
  cases hU
  cases hH
  cases hi
  cases hc
  exact h

lemma enrichedRightLaw_of_heq {U H U' H' : V} (hU : U = U') (hH : H = H')
    (i : 𝟙_ V ⟶ U) (i' : 𝟙_ V ⟶ U') (c : H ⊗ U ⟶ H) (c' : H' ⊗ U' ⟶ H')
    (hi : HEq i i') (hc : HEq c c')
    (h : (ρ_ H').inv ≫ H' ◁ i' ≫ c' = 𝟙 H') :
    (ρ_ H).inv ≫ H ◁ i ≫ c = 𝟙 H := by
  cases hU
  cases hH
  cases hi
  cases hc
  exact h

lemma enrichedAssocLaw_of_heq {A B C D E F A' B' C' D' E' F' : V}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D') (hE : E = E') (hF : F = F')
    (p : A ⊗ B ⟶ D) (q : D ⊗ C ⟶ F) (r : B ⊗ C ⟶ E) (s : A ⊗ E ⟶ F)
    (p' : A' ⊗ B' ⟶ D') (q' : D' ⊗ C' ⟶ F') (r' : B' ⊗ C' ⟶ E') (s' : A' ⊗ E' ⟶ F')
    (hp : HEq p p') (hq : HEq q q') (hr : HEq r r') (hs : HEq s s')
    (h : (α_ A' B' C').inv ≫ p' ▷ C' ≫ q' = A' ◁ r' ≫ s') :
    (α_ A B C).inv ≫ p ▷ C ≫ q = A ◁ r ≫ s := by
  cases hA
  cases hB
  cases hC
  cases hD
  cases hE
  cases hF
  cases hp
  cases hq
  cases hr
  cases hs
  exact h

lemma enrichedFunctorUnitLaw_of_heq {A B A' B' : V} (hA : A = A') (hB : B = B')
    (i : 𝟙_ V ⟶ A) (j : 𝟙_ V ⟶ B) (f : A ⟶ B)
    (i' : 𝟙_ V ⟶ A') (j' : 𝟙_ V ⟶ B') (f' : A' ⟶ B')
    (hi : HEq i i') (hj : HEq j j') (hf : HEq f f') (h : i' ≫ f' = j') :
    i ≫ f = j := by
  cases hA
  cases hB
  cases hi
  cases hj
  cases hf
  exact h

lemma enrichedFunctorCompLaw_of_heq {A B C U V' W A' B' C' U' V'' W' : V}
    (hA : A = A') (hB : B = B') (hC : C = C')
    (hU : U = U') (hV : V' = V'') (hW : W = W')
    (p : A ⊗ B ⟶ C) (q : U ⊗ V' ⟶ W) (f : A ⟶ U) (g : B ⟶ V') (k : C ⟶ W)
    (p' : A' ⊗ B' ⟶ C') (q' : U' ⊗ V'' ⟶ W')
    (f' : A' ⟶ U') (g' : B' ⟶ V'') (k' : C' ⟶ W')
    (hp : HEq p p') (hq : HEq q q') (hf : HEq f f')
    (hg : HEq g g') (hk : HEq k k') (h : p' ≫ k' = (f' ⊗ₘ g') ≫ q') :
    p ≫ k = (f ⊗ₘ g) ≫ q := by
  cases hA
  cases hB
  cases hC
  cases hU
  cases hV
  cases hW
  cases hp
  cases hq
  cases hf
  cases hg
  cases hk
  exact h

end SerrePositivity.DifferentialGraded

end EnrichedLawTransport

/-! ## CategorySigma（旧 SerrePositivity/DifferentialGraded/Presentation/CategorySigma.lean） -/

/-!
概要：固定基底を共有する dg 圏提示データの非連結和を構成する。
方針：同じ成分の Hom を保ち、異なる成分の Hom は零提示にする。
規約：対象集合の ordinal への再添字と seed の延長は別に行う。
使われ方：二項・可算個の出発提示の同時精密化の対象側。
-/

@[expose] public section CategorySigma
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (R : Type u) [CommRing R] (B J : Type u) (X : J → Type u)
  (c : ∀ j, DGCategoryPresentationData R B (X j))
local instance : DecidableEq J := Classical.decEq J

namespace DGCategoryPresentationData

def sigmaHom (x y : Sigma X) : DGComplexPresentationCode R B :=
  if h : x.1 = y.1 then (c x.1).hom x.2 (h.symm ▸ y.2) else DGComplexPresentationCode.zero R B

lemma sigmaHom_same (j : J) (x y : X j) :
    sigmaHom R B J X c ⟨j, x⟩ ⟨j, y⟩ = (c j).hom x y := by simp [sigmaHom]

lemma sigmaHom_value_same (j : J) (x y : X j) :
    (sigmaHom R B J X c ⟨j, x⟩ ⟨j, y⟩).value R B = ((c j).hom x y).value R B :=
  congrArg (DGComplexPresentationCode.value R B) (sigmaHom_same R B J X c j x y)

lemma sigmaHom_isZero_ne {j k : J} (h : j ≠ k) (x : X j) (y : X k) :
    IsZero ((sigmaHom R B J X c ⟨j, x⟩ ⟨k, y⟩).value R B) := by
  simpa [sigmaHom, h] using DGComplexPresentationCode.zero_value_isZero R B

def sigmaUnit (x : Sigma X) : 𝟙_ (Complex R) ⟶ (sigmaHom R B J X c x x).value R B := by
  rcases x with ⟨j, x⟩
  exact cast (congrArg (fun h : DGComplexPresentationCode R B =>
    𝟙_ (Complex R) ⟶ h.value R B) (sigmaHom_same R B J X c j x x).symm) ((c j).unit x)

def sigmaComp (x y z : Sigma X) :
    (sigmaHom R B J X c x y).value R B ⊗ (sigmaHom R B J X c y z).value R B ⟶
      (sigmaHom R B J X c x z).value R B := by
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  rcases z with ⟨l, z⟩
  by_cases h : j = k
  · subst k
    by_cases h' : j = l
    · subst l
      exact cast (by simp only [sigmaHom_same]) ((c j).comp x y z)
    · exact 0
  · exact 0

lemma sigmaUnit_heq (j : J) (x : X j) :
    HEq (sigmaUnit R B J X c ⟨j, x⟩) ((c j).unit x) := by
  dsimp only [sigmaUnit]
  exact cast_heq _ _

lemma sigmaComp_heq (j : J) (x y z : X j) :
    HEq (sigmaComp R B J X c ⟨j, x⟩ ⟨j, y⟩ ⟨j, z⟩) ((c j).comp x y z) := by
  dsimp only [sigmaComp]
  split_ifs <;> first | exact cast_heq _ _ | contradiction

lemma sigmaLeft (x y : Sigma X) :
    (λ_ ((sigmaHom R B J X c x y).value R B)).inv ≫
      sigmaUnit R B J X c x ▷ _ ≫ sigmaComp R B J X c x x y = 𝟙 _ := by
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  by_cases h : j = k
  · subst k
    exact enrichedLeftLaw_of_heq
      (sigmaHom_value_same R B J X c j x x) (sigmaHom_value_same R B J X c j x y)
      _ _ _ _ (sigmaUnit_heq R B J X c j x) (sigmaComp_heq R B J X c j x x y)
      ((c j).left x y)
  · exact (sigmaHom_isZero_ne R B J X c h x y).eq_of_tgt _ _

lemma sigmaRight (x y : Sigma X) :
    (ρ_ ((sigmaHom R B J X c x y).value R B)).inv ≫
      _ ◁ sigmaUnit R B J X c y ≫ sigmaComp R B J X c x y y = 𝟙 _ := by
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  by_cases h : j = k
  · subst k
    exact enrichedRightLaw_of_heq
      (sigmaHom_value_same R B J X c j y y) (sigmaHom_value_same R B J X c j x y)
      _ _ _ _ (sigmaUnit_heq R B J X c j y) (sigmaComp_heq R B J X c j x y y)
      ((c j).right x y)
  · exact (sigmaHom_isZero_ne R B J X c h x y).eq_of_tgt _ _

lemma sigmaAssoc (w x y z : Sigma X) :
    (α_ _ _ _).inv ≫ sigmaComp R B J X c w x y ▷ _ ≫ sigmaComp R B J X c w y z =
      _ ◁ sigmaComp R B J X c x y z ≫ sigmaComp R B J X c w x z := by
  rcases w with ⟨i, w⟩
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  rcases z with ⟨l, z⟩
  by_cases h₁ : i = j
  · subst j
    by_cases h₂ : i = k
    · subst k
      by_cases h₃ : i = l
      · subst l
        exact enrichedAssocLaw_of_heq
          (sigmaHom_value_same R B J X c i w x) (sigmaHom_value_same R B J X c i x y)
          (sigmaHom_value_same R B J X c i y z) (sigmaHom_value_same R B J X c i w y)
          (sigmaHom_value_same R B J X c i x z) (sigmaHom_value_same R B J X c i w z)
          _ _ _ _ _ _ _ _ (sigmaComp_heq R B J X c i w x y)
          (sigmaComp_heq R B J X c i w y z) (sigmaComp_heq R B J X c i x y z)
          (sigmaComp_heq R B J X c i w x z) ((c i).assoc w x y z)
      · exact ((tensorLeft ((sigmaHom R B J X c ⟨i, w⟩ ⟨i, x⟩).value R B)).map_isZero
          ((tensorLeft ((sigmaHom R B J X c ⟨i, x⟩ ⟨i, y⟩).value R B)).map_isZero
            (sigmaHom_isZero_ne R B J X c h₃ y z))).eq_of_src _ _
    · exact ((tensorLeft ((sigmaHom R B J X c ⟨i, w⟩ ⟨i, x⟩).value R B)).map_isZero
        ((tensorRight ((sigmaHom R B J X c ⟨k, y⟩ ⟨l, z⟩).value R B)).map_isZero
          (sigmaHom_isZero_ne R B J X c h₂ x y))).eq_of_src _ _
  · exact ((tensorRight
      ((sigmaHom R B J X c ⟨j, x⟩ ⟨k, y⟩).value R B ⊗
        (sigmaHom R B J X c ⟨k, y⟩ ⟨l, z⟩).value R B)).map_isZero
        (sigmaHom_isZero_ne R B J X c h₁ w x)).eq_of_src _ _

def sigma : DGCategoryPresentationData R B (Sigma X) where
  hom := sigmaHom R B J X c
  unit := sigmaUnit R B J X c
  comp := sigmaComp R B J X c
  left := sigmaLeft R B J X c
  right := sigmaRight R B J X c
  assoc := sigmaAssoc R B J X c

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
end

end CategorySigma

/-! ## CategorySigmaDesc（旧 SerrePositivity/DifferentialGraded/Presentation/CategorySigmaDesc.lean） -/

/-!
概要：各出発提示からの dg 関手を非連結和からの一つの関手へまとめる。
方針：同じ成分の鎖写像を等式移送し、異成分には零鎖写像を使う。
規約：元の成分内の Hom 作用を保持し、標的の Small 性を要求しない。
使われ方：異なる arrow の二項・可算直和に必要な共通評価関手。
-/

@[expose] public section CategorySigmaDesc
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (R : Type u) [CommRing R] (B J : Type u) (X : J → Type u)
  (c : ∀ j, DGCategoryPresentationData R B (X j)) (D : Type v) [DGCategory R D]
variable (F : ∀ j, letI := (c j).enrichment R B (X j); DGFunctor R (X j) D)
namespace DGCategoryPresentationData

def sigmaDescMap (x y : Sigma X) :
    letI (j : J) := (c j).enrichment R B (X j)
    (sigmaHom R B J X c x y).value R B ⟶ (F x.1).obj x.2 ⟶[Complex R] (F y.1).obj y.2 := by
  letI (j : J) := (c j).enrichment R B (X j)
  classical
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  by_cases h : j = k
  · subst k
    exact eqToHom (sigmaHom_value_same R B J X c j x y) ≫ (F j).map x y
  · exact 0

lemma sigmaDescMap_heq (j : J) (x y : X j) :
    letI (j : J) := (c j).enrichment R B (X j)
    HEq (sigmaDescMap R B J X c D F ⟨j, x⟩ ⟨j, y⟩) ((F j).map x y) := by
  letI (j : J) := (c j).enrichment R B (X j)
  classical
  dsimp only [sigmaDescMap]
  split_ifs <;> first | exact eqToHom_comp_heq _ _ | contradiction

def sigmaDesc :
    letI (j : J) := (c j).enrichment R B (X j)
    letI := (sigma R B J X c).enrichment R B (Sigma X)
    DGFunctor R (Sigma X) D := by
  letI (j : J) := (c j).enrichment R B (X j)
  letI := (sigma R B J X c).enrichment R B (Sigma X)
  exact {
    obj x := (F x.1).obj x.2
    map := sigmaDescMap R B J X c D F
    map_id x := by
      rcases x with ⟨j, x⟩
      exact enrichedFunctorUnitLaw_of_heq
        (sigmaHom_value_same R B J X c j x x) rfl
        _ _ _ _ _ _ (sigmaUnit_heq R B J X c j x) (HEq.rfl)
        (sigmaDescMap_heq R B J X c D F j x x) ((F j).map_id x)
    map_comp x y z := by
      rcases x with ⟨j, x⟩
      rcases y with ⟨k, y⟩
      rcases z with ⟨l, z⟩
      by_cases h₁ : j = k
      · subst k
        by_cases h₂ : j = l
        · subst l
          exact enrichedFunctorCompLaw_of_heq
            (sigmaHom_value_same R B J X c j x y)
            (sigmaHom_value_same R B J X c j y z)
            (sigmaHom_value_same R B J X c j x z) rfl rfl rfl
            _ _ _ _ _ _ _ _ _ _ (sigmaComp_heq R B J X c j x y z) (HEq.rfl)
            (sigmaDescMap_heq R B J X c D F j x y)
            (sigmaDescMap_heq R B J X c D F j y z)
            (sigmaDescMap_heq R B J X c D F j x z) ((F j).map_comp x y z)
        · exact ((tensorLeft ((sigmaHom R B J X c ⟨j, x⟩ ⟨j, y⟩).value R B)).map_isZero
            (sigmaHom_isZero_ne R B J X c h₂ y z)).eq_of_src _ _
      · exact ((tensorRight ((sigmaHom R B J X c ⟨k, y⟩ ⟨l, z⟩).value R B)).map_isZero
          (sigmaHom_isZero_ne R B J X c h₁ x y)).eq_of_src _ _ }

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
end

end CategorySigmaDesc

/-! ## CategorySigmaInclusion（旧 SerrePositivity/DifferentialGraded/Presentation/CategorySigmaInclusion.lean） -/

/-!
概要：非連結和の各成分を、全 Hom の同型を保持して包含する。
方針：同一成分の Hom 提示の等式で恒等鎖写像を移送し、三法則を抽象移送する。
規約：異成分の Hom を埋める追加データは要求しない。
使われ方：異なる出発提示の seed を共通の出発圏へ延長する包含。
-/

@[expose] public section CategorySigmaInclusion
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (B J : Type u) (X : J → Type u)
  (c : ∀ j, DGCategoryPresentationData R B (X j))
namespace DGCategoryPresentationData

def sigmaInclusionMap (j : J) (x y : X j) :
    ((c j).hom x y).value R B ⟶ (sigmaHom R B J X c ⟨j, x⟩ ⟨j, y⟩).value R B :=
  eqToHom (sigmaHom_value_same R B J X c j x y).symm

lemma sigmaInclusionMap_heq (j : J) (x y : X j) :
    HEq (sigmaInclusionMap R B J X c j x y) (𝟙 (((c j).hom x y).value R B)) := by
  unfold sigmaInclusionMap
  exact eqToHom_heq_id_dom _ _ _

def sigmaInclusion (j : J) :
    letI := (c j).enrichment R B (X j)
    letI := (sigma R B J X c).enrichment R B (Sigma X)
    DGFunctor R (X j) (Sigma X) := by
  letI := (c j).enrichment R B (X j)
  letI := (sigma R B J X c).enrichment R B (Sigma X)
  exact {
    obj := Sigma.mk j
    map := sigmaInclusionMap R B J X c j
    map_id x := enrichedFunctorUnitLaw_of_heq rfl
      (sigmaHom_value_same R B J X c j x x)
      _ _ _ _ _ _ (HEq.rfl) (sigmaUnit_heq R B J X c j x)
      (sigmaInclusionMap_heq R B J X c j x x) (Category.comp_id _)
    map_comp x y z := enrichedFunctorCompLaw_of_heq rfl rfl rfl
      (sigmaHom_value_same R B J X c j x y)
      (sigmaHom_value_same R B J X c j y z)
      (sigmaHom_value_same R B J X c j x z)
      _ _ _ _ _ _ _ _ _ _ (HEq.rfl) (sigmaComp_heq R B J X c j x y z)
      (sigmaInclusionMap_heq R B J X c j x y)
      (sigmaInclusionMap_heq R B J X c j y z)
      (sigmaInclusionMap_heq R B J X c j x z)
      (by
        change (c j).comp x y z ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ (c j).comp x y z
        simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]) }

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
end

end CategorySigmaInclusion

/-! ## CategorySigmaComponents（旧 SerrePositivity/DifferentialGraded/Presentation/CategorySigmaComponents.lean） -/

/-!
概要：非連結和からの共通評価を各成分へ制限すると元の dg 関手に厳密に一致する。
方針：同一成分の二つの等式移送が互いに逆であることを全 Hom で検証する。
規約：対象と全次数の作用を比較し、ホモトピー圏だけの一致で代用しない。
使われ方：出発提示の同時精密化と元の arrow の延長比較。
-/

@[expose] public section CategorySigmaComponents
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (B J : Type u) (X : J → Type u)
  (c : ∀ j, DGCategoryPresentationData R B (X j)) (D : Type v) [DGCategory R D]
  (F : ∀ j, letI := (c j).enrichment R B (X j); DGFunctor R (X j) D)
namespace DGCategoryPresentationData

lemma sigmaDescMap_same (j : J) (x y : X j) :
    letI (j : J) := (c j).enrichment R B (X j)
    sigmaDescMap R B J X c D F ⟨j, x⟩ ⟨j, y⟩ =
      eqToHom (sigmaHom_value_same R B J X c j x y) ≫ (F j).map x y := by
  classical
  dsimp only [sigmaDescMap]
  split_ifs <;> first | rfl | contradiction

lemma sigmaInclusion_comp_sigmaDesc (j : J) :
    letI (j : J) := (c j).enrichment R B (X j)
    letI := (sigma R B J X c).enrichment R B (Sigma X)
    (sigmaInclusion R B J X c j).comp (sigmaDesc R B J X c D F) = F j := by
  letI (j : J) := (c j).enrichment R B (X j)
  letI := (sigma R B J X c).enrichment R B (Sigma X)
  apply EnrichedFunctor.ext (Complex R)
    (F := (sigmaInclusion R B J X c j).comp (sigmaDesc R B J X c D F))
    (G := F j) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change sigmaInclusionMap R B J X c j x y ≫
    sigmaDescMap R B J X c D F ⟨j, x⟩ ⟨j, y⟩ = (F j).map x y
  rw [sigmaDescMap_same]
  simp only [sigmaInclusionMap, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
end

end CategorySigmaComponents

/-! ## GeneratedHomSphereArrowLift（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomSphereArrowLift.lean） -/

/-!
概要：元の Hom 係数を含むκコードで、任意シフト自由 sphere 間の閉射を持ち上げる。
方針：閉斉次係数をコードへ持ち上げ、同じ次数の cycle から自由 sphere 閉射を逆構成する。
規約：係数の評価後の厳密一致を証明し、実延長の端点同型との比較は別工程とする。
使われ方：c′ の全シフト自由行列の各係数の共通源持ち上げ。
-/

@[expose] public section GeneratedHomSphereArrowLift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
variable (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ)
  (n m : ℤ)
  (f : freeSphere R D (value x) n ⟶ freeSphere R D (value y) m)
  (hf : freeSphereClosedCoefficient R D (value x) (value y) n m f ∈
    linearSpan source target degree R D value coefficient x y (n - m))

def codeFreeSphereClosedArrow :
    freeSphere R ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x n ⟶
      freeSphere R ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) y m :=
  freeSphereClosedCoefficientPreimage R
    ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x y n m
    ⟨codeCochainLift R D κ a source target degree value coefficient hκ hI x y (n - m)
      (freeSphereClosedCoefficient R D (value x) (value y) n m f) hf,
      codeCochainLift_differential R D κ a source target degree value coefficient hκ hI x y (n - m)
        (freeSphereClosedCoefficient R D (value x) (value y) n m f) hf
        (freeSphereClosedCoefficient_closed R D (value x) (value y) n m f)⟩

lemma codeFreeSphereClosedArrow_coefficient_map :
    ((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f (n - m)
      (freeSphereClosedCoefficient R
        ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x y n m
        (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf)) =
      freeSphereClosedCoefficient R D (value x) (value y) n m f := by
  rw [codeFreeSphereClosedArrow, freeSphereClosedCoefficientPreimage_coefficient]
  exact codeCochainLift_map R D κ a source target degree value coefficient hκ hI x y (n - m) _ hf

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomSphereArrowLift

/-! ## GeneratedHomSphereExtensionComparison（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomSphereExtensionComparison.lean） -/

/-!
概要：コード内に持ち上げた任意シフト自由閉射を、実延長の端点同型付きで元の閉射へ比較する。
方針：元の Hom 係数で自由閉射を検出し、自由延長の自然性へ接続する。
規約：元の閉射全体と同じ実端点同型を保持する。
使われ方：c′ の全シフト自由閉射族の共通源精密化。
-/

@[expose] public section GeneratedHomSphereExtensionComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
local notation "C" => (DGCategoryPresentationCode.Objects R κ
  (code R D κ a source target degree value coefficient hκ hI))
local notation "L" => codeEvaluation R D κ a source target degree value coefficient hκ hI
lemma codeFreeSphereClosedArrow_image (x y : C) (n m : ℤ)
    (f : freeSphere R D (value x) n ⟶ freeSphere R D (value y) m)
    (hf : freeSphereClosedCoefficient R D (value x) (value y) n m f ∈
      linearSpan source target degree R D value coefficient x y (n - m)) :
    dgFreeClosedArrowImage R C D L x y (complexSphere R n) (complexSphere R m)
      (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf) = f := by
  apply freeSphereClosedCoefficient_injective R D (value x) (value y) n m
  exact (dgFreeClosedArrowImage_sphere_coefficient R C D L x y n m
    (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf)).trans
    (codeFreeSphereClosedArrow_coefficient_map R D κ a source target degree value coefficient
      hκ hI x y n m f hf)

lemma codeFreeSphereClosedArrow_extension_comm (x y : C) (n m : ℤ)
    (f : freeSphere R D (value x) n ⟶ freeSphere R D (value y) m)
    (hf : freeSphereClosedCoefficient R D (value x) (value y) n m f ∈
      linearSpan source target degree R D value coefficient x y (n - m)) :
    (dgModuleExtension R C D L).onClosed.map
      (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf) ≫
      (dgModuleExtensionFreeAtIso R C D L y (complexSphere R m)).hom =
    (dgModuleExtensionFreeAtIso R C D L x (complexSphere R n)).hom ≫ f := by
  have h := dgModuleExtensionFreeAtIso_arrow_comm R C D L x y
    (complexSphere R n) (complexSphere R m)
    (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf)
  rw [codeFreeSphereClosedArrow_image R D κ a source target degree value coefficient
    hκ hI x y n m f hf] at h
  exact h

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomSphereExtensionComparison

/-! ## GeneratedHomSphereMatrixLift（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomSphereMatrixLift.lean） -/

/-!
概要：コードの全シフト自由閉射行列を、実延長と直和端点の同型付きで元の行列へ比較する。
方針：support 内の係数を持ち上げ、各成分の可換式を余積と有限和で束ねる。
規約：元の閉射行列全体の等式を証明し、support 外の係数は零とする。
使われ方：c′ の自由 seed 間閉射の共通源精密化。
-/

@[expose] public section GeneratedHomSphereMatrixLift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
local notation "C" => (DGCategoryPresentationCode.Objects R κ
  (code R D κ a source target degree value coefficient hκ hI))
local notation "L" => codeEvaluation R D κ a source target degree value coefficient hκ hI

structure SphereMatrixData (J K : Type u) where
  x : J → C
  y : K → C
  n : J → ℤ
  m : K → ℤ
  support : J → Finset K
  arrow : ∀ i j, freeSphere R D (value (x i)) (n i) ⟶ freeSphere R D (value (y j)) (m j)
  contained : ∀ i j, j ∈ support i →
    freeSphereClosedCoefficient R D (value (x i)) (value (y j)) (n i) (m j) (arrow i j) ∈
      linearSpan source target degree R D value coefficient (x i) (y j) (n i - m j)

variable {J K : Type u}
local notation "Data" => SphereMatrixData R D κ a source target degree value coefficient hκ hI J K

def codeSphereMatrixEntry (p : Data) (i : J) (j : K) :
    freeSphere R C (p.x i) (p.n i) ⟶ freeSphere R C (p.y j) (p.m j) := by
  classical
  exact if h : j ∈ p.support i then
    codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI
      (p.x i) (p.y j) (p.n i) (p.m j) (p.arrow i j) (p.contained i j h)
    else 0

def codeSphereMatrixLift (p : Data) :
    (∐ fun i => freeSphere R C (p.x i) (p.n i)) ⟶ ∐ fun j => freeSphere R C (p.y j) (p.m j) :=
  Sigma.desc (fun i => ∑ j ∈ p.support i,
    codeSphereMatrixEntry R D κ a source target degree value coefficient hκ hI p i j ≫
      Sigma.ι (fun j => freeSphere R C (p.y j) (p.m j)) j)

set_option maxRecDepth 1024 in
lemma codeSphereMatrixLift_extension_comm (p : Data) :
    let F := (dgModuleExtension R C D L).onClosed
    letI : PreservesColimitsOfSize.{u, u} F :=
      (dgModuleExtensionRestrictionAdjunction R C D L).leftAdjoint_preservesColimits
    F.map (codeSphereMatrixLift R D κ a source target degree value coefficient hκ hI p) ≫
      (coproductFamilyImageIso F (fun j => freeSphere R C (p.y j) (p.m j))
        (fun j => freeSphere R D (value (p.y j)) (p.m j))
        (fun j => dgModuleExtensionFreeAtIso R C D L (p.y j) (complexSphere R (p.m j)))).hom =
    (coproductFamilyImageIso F (fun i => freeSphere R C (p.x i) (p.n i))
      (fun i => freeSphere R D (value (p.x i)) (p.n i))
      (fun i => dgModuleExtensionFreeAtIso R C D L (p.x i) (complexSphere R (p.n i)))).hom ≫
    Sigma.desc (fun i => ∑ j ∈ p.support i, p.arrow i j ≫
      Sigma.ι (fun j => freeSphere R D (value (p.y j)) (p.m j)) j) := by
  classical
  dsimp only
  letI : PreservesColimitsOfSize.{u, u} (dgModuleExtension R C D L).onClosed :=
    (dgModuleExtensionRestrictionAdjunction R C D L).leftAdjoint_preservesColimits
  apply coproductFamilyImageIso_matrix
  intro i j hj
  simp only [codeSphereMatrixEntry, dif_pos hj]
  exact codeFreeSphereClosedArrow_extension_comm R D κ a source target degree value coefficient
    hκ hI (p.x i) (p.y j) (p.n i) (p.m j) (p.arrow i j) (p.contained i j hj)

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomSphereMatrixLift

/-! ## GeneratedHomAugmentedSphereFamily（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomAugmentedSphereFamily.lean） -/

/-!
概要：κ個以下の全シフト自由 sphere 間閉射を、一つの係数コードへ同時に持ち上げる。
方針：各閉射の次数 n-m の係数を元の出発関手の全基底像に併合する。
規約：元の全 Hom の厳密因子化と、各持ち上げ閉射の係数評価の厳密一致を保持する。
使われ方：c′ の行有限自由行列の support 全体を共通源へ取り込む。
-/

@[expose] public section GeneratedHomAugmentedSphereFamily
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  (a : κ.ord.ToType) {K : Type u} (D : Type v) [DGCategory R D] [Small.{u} D]
  (value : Set.Iio a → D) (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))
  (source target : K → Set.Iio a) (n m : K → ℤ)
  (f : ∀ k, freeSphere R D (value (source k)) (n k) ⟶
    freeSphere R D (value (target k)) (m k))
  (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ)

def dgSphereFamilyCoefficient (k : K) :
    GradedHom R (value (source k)) (value (target k)) (n k - m k) :=
  freeSphereClosedCoefficient R D (value (source k)) (value (target k)) (n k) (m k) (f k)

local notation "S" => dgCodeAugmentedSource R κ c D value F source
local notation "T" => dgCodeAugmentedTarget R κ c D value F target
local notation "N" => dgCodeAugmentedDegree R κ c (fun k => n k - m k)
local notation "P" => dgCodeAugmentedCoefficient R κ c D value F source target
  (fun k => n k - m k) (dgSphereFamilyCoefficient R κ a D value source target n m f)
local notation "hB" => dgCodeAugmentedCoefficientIndex_cardinal_le R κ c hκ hK

def dgSphereFamilySourceCode : DGCategoryPresentationCode R κ :=
  DGGeneratedHomWord.code R D κ a S T N value P hκ hB

def dgSphereFamilySourceEvaluation : DGFunctor R
    ((dgSphereFamilySourceCode R κ c a D value F source target n m f hκ hK).Objects R κ) D :=
  DGGeneratedHomWord.codeEvaluation R D κ a S T N value P hκ hB

def dgSphereFamilySourceInclusion : DGFunctor R (c.Objects R κ)
    ((dgSphereFamilySourceCode R κ c a D value F source target n m f hκ hK).Objects R κ) :=
  dgAugmentedSourceCodeInclusion R κ c a D value F source target (fun k => n k - m k)
    (dgSphereFamilyCoefficient R κ a D value source target n m f) hκ hK

lemma dgSphereFamilySourceInclusion_comp_evaluation :
    (dgSphereFamilySourceInclusion R κ c a D value F source target n m f hκ hK).comp
      (dgSphereFamilySourceEvaluation R κ c a D value F source target n m f hκ hK) =
    F.comp (dgObjectImageEvaluation R value) :=
  dgAugmentedSourceCodeInclusion_comp_evaluation R κ c a D value F source target
    (fun k => n k - m k) (dgSphereFamilyCoefficient R κ a D value source target n m f) hκ hK

local notation "C" => (DGCategoryPresentationCode.Objects R κ
  (dgSphereFamilySourceCode R κ c a D value F source target n m f hκ hK))

def dgSphereFamilySourceArrow (k : K) :
    freeSphere R C (source k) (n k) ⟶ freeSphere R C (target k) (m k) :=
  DGGeneratedHomWord.codeFreeSphereClosedArrow R D κ a S T N value P hκ hB
    (source k) (target k) (n k) (m k) (f k)
    (dgCodeAugmentedCoefficient_mem R κ c D value F source target (fun k => n k - m k)
      (dgSphereFamilyCoefficient R κ a D value source target n m f) k)

lemma dgSphereFamilySourceArrow_coefficient_map (k : K) :
    ((dgSphereFamilySourceEvaluation R κ c a D value F source target n m f hκ hK).map
      (source k) (target k)).f (n k - m k)
      (freeSphereClosedCoefficient R C (source k) (target k) (n k) (m k)
        (dgSphereFamilySourceArrow R κ c a D value F source target n m f hκ hK k)) =
      freeSphereClosedCoefficient R D (value (source k)) (value (target k)) (n k) (m k) (f k) :=
  DGGeneratedHomWord.codeFreeSphereClosedArrow_coefficient_map R D κ a S T N value P hκ hB
    (source k) (target k) (n k) (m k) (f k)
    (dgCodeAugmentedCoefficient_mem R κ c D value F source target (fun k => n k - m k)
      (dgSphereFamilyCoefficient R κ a D value source target n m f) k)

end SerrePositivity.DifferentialGraded
end

end GeneratedHomAugmentedSphereFamily

/-! ## GeneratedHomClosedFamilyRepresentables（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomClosedFamilyRepresentables.lean） -/

/-!
概要：同時に持ち上げた閉射を、実延長した代表加群間の同じ閉射へ比較する。
方針：代表延長同型の自然性と閉射族の厳密な評価式を合成する。
規約：端点には元の代表延長同型を使い、元の閉射を別の射へ置き換えない。
使われ方：c′ の cone 精密化の代表加群の場合の第一辺比較。
-/

@[expose] public section GeneratedHomClosedFamilyRepresentables
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  (a : κ.ord.ToType) {K : Type u} (D : Type v) [DGCategory R D] [Small.{u} D]
  (value : Set.Iio a → D)
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))
  (source target : K → Set.Iio a)
  (f : ∀ k, ForgetEnrichment.of (Complex R) (value (source k)) ⟶
    ForgetEnrichment.of (Complex R) (value (target k)))
  (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ)

local notation "C" => (DGCategoryPresentationCode.Objects R κ (dgClosedFamilySourceCode R κ c a D value F source target f hκ hK))
local notation "L" => dgClosedFamilySourceEvaluation R κ c a D value F source target f hκ hK
local notation "g" => dgClosedFamilySourceArrow R κ c a D value F source target f hκ hK

lemma dgClosedFamilySourceRepresentableArrow_comm (k : K) :
    (dgModuleExtension R C D L).onClosed.map ((dgYoneda R C).onClosed.map (g k)) ≫
      (dgModuleExtensionRepresentableIso R C D L (target k)).hom =
    (dgModuleExtensionRepresentableIso R C D L (source k)).hom ≫
      (dgYoneda R D).onClosed.map (f k) := by
  have h := dgModuleExtensionRepresentableIso_closed_naturality R C D L (g k)
  rw [dgClosedFamilySourceArrow_map] at h
  exact h

end SerrePositivity.DifferentialGraded
end

end GeneratedHomClosedFamilyRepresentables
