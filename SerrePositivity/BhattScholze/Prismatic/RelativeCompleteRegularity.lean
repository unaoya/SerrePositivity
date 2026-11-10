module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.HomologicalAlgebra.KoszulAlgebraTorComparison
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# 古典環の相対完全正則性

## 概要
BS 著者版 Definition 2.42 の古典環の場合を、通常の Koszul ホモロジーで表す。

## 方針
係数拡大と列の付加から Koszul 複体の標準射を作る。零次の平坦性と、
高次での剰余環上のテンソル比較を要求する。

## 規約
有限列を指定する。導来完備性は指定列の各元に関して課す。

## 使われ方
向き付き prism の係数環に対する prismatic envelope の入力条件。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory DerivedCompletion
open scoped TensorProduct

variable {A B : Type u} [CommRing A] [CommRing B]
variable [Algebra A B] {n r : ℕ}

/-- 指定された順序で基底の列に追加の列をつなぐ。 -/
def appendKoszulCoordinates {R : Type u} (a : Fin n → R) :
    {r : ℕ} → (Fin r → R) → Fin (n + r) → R
  | 0, _ => a
  | _ + 1, x => Fin.snoc (appendKoszulCoordinates a (Fin.init x)) (x (Fin.last _))

private theorem range_le_appendKoszulCoordinates {R : Type u} (a : Fin n → R) :
    ∀ {r : ℕ} (x : Fin r → R), Set.range a ⊆ Set.range (appendKoszulCoordinates a x)
  | 0, _ => le_rfl
  | _ + 1, x => by
    intro y hy
    obtain ⟨j, hj⟩ := range_le_appendKoszulCoordinates a (Fin.init x) hy
    exact ⟨j.castSucc, by simpa [appendKoszulCoordinates, Fin.snoc_castSucc] using hj⟩

/-- 概要：列の付加に対応する Koszul 複体の標準射。
方針：追加の各座標について写像錐の右側への包含を合成する。
規約：BS 著者版 Definition 2.42 の列の順序。
使われ方：相対完全正則性のホモロジー比較。 -/
def koszulAppendMap {R : Type u} [CommRing R] (a : Fin n → R) :
    {r : ℕ} → (x : Fin r → R) → koszulComplex a ⟶ koszulComplex (appendKoszulCoordinates a x)
  | 0, _ => 𝟙 _
  | k + 1, x => by
    let b := appendKoszulCoordinates a (Fin.init x)
    let t := x (Fin.last _)
    let c : Fin (n + k + 1) → R := Fin.snoc b t
    have h : b = Fin.init c := (Fin.init_snoc (α := fun _ : Fin (n + k + 1) ↦ R) t b).symm
    change koszulComplex a ⟶ koszulComplex c
    exact koszulAppendMap a (Fin.init x) ≫
      eqToHom (congrArg koszulComplex h) ≫
        CochainComplex.mappingCone.inr (smulId (c (Fin.last _)) (koszulComplex (Fin.init c)))

/-- Koszul ホモロジーに作用する零次の剰余環。 -/
abbrev KoszulResidue {R : Type u} [CommRing R] (a : Fin n → R) :=
  R ⧸ Ideal.span (Set.range a)

local notation "z[" a "," x "]" => appendKoszulCoordinates (algebraMap _ _ ∘ a) x

/-- 基底の座標が追加列を含むイデアルに入ることによる剰余環射。 -/
def relativeKoszulResidueMap (a : Fin n → A) (x : Fin r → B) :
    KoszulResidue a →+* KoszulResidue z[a,x] :=
  Ideal.quotientMap _ (algebraMap A B) (by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span (range_le_appendKoszulCoordinates (algebraMap A B ∘ a) x ⟨i, rfl⟩))

private theorem koszulHomology_torsion {R : Type u} [CommRing R] (a : Fin n → R) (q : ℤ) :
    Module.IsTorsionBySet R ((koszulComplex a).homology q) (Ideal.span (Set.range a)) := by
  rw [koszulComplex_eq_functor]
  intro y ⟨b, hb⟩
  exact Module.mem_annihilator.mp
    (span_le_annihilator_koszulModuleHomology a (ModuleCat.of R R) q hb) y

/-- 概要：Koszul ホモロジー上の零次剰余環の作用。
方針：座標の零ホモトピーから、列の生成イデアルが作用を零にする。
規約：標準の環作用を商に降ろす。
使われ方：BS 著者版 Definition 2.42 の比較テンソル積。 -/
@[instance_reducible] def koszulResidueModule {R : Type u} [CommRing R] (a : Fin n → R) (q : ℤ) :
    Module (KoszulResidue a) ((koszulComplex a).homology q) :=
  (koszulHomology_torsion a q).module

private def relativeKoszulComplexMap (a : Fin n → A) (x : Fin r → B) :
    koszulComplex a ⟶
      ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj
        (koszulComplex z[a,x]) :=
  let φ := algebraMap A B
  let U := (ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)
  let η := (ModuleCat.extendRestrictScalarsAdj φ).unit.mapHomologicalComplex (.up ℤ)
  η.app (koszulComplex a) ≫ U.map
    ((baseChangeKoszulIso φ a).hom ≫ koszulAppendMap (φ ∘ a) x)

private def relativeKoszulHomologyMap (a : Fin n → A) (x : Fin r → B) (q : ℤ) :
    (koszulComplex a).homology q ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj ((koszulComplex z[a,x]).homology q) :=
  HomologicalComplex.homologyMap (relativeKoszulComplexMap a x) q ≫
    (restrictCochainHomologyIso (R := A) (C := B) q).hom.app (koszulComplex z[a,x])

/-- 概要：標準の Koszul ホモロジー比較射。
方針：係数拡大と列の付加が誘導する射を剰余環上の線形射に降ろし、
スカラー拡大の随伴でテンソル積からの射を得る。
規約：BS 著者版 Definition 2.42 の古典環版。次数 q は余鎖次数。
使われ方：相対完全正則性の定義。 -/
def relativeKoszulComparison (a : Fin n → A) (x : Fin r → B) (q : ℤ) :
    letI := (relativeKoszulResidueMap a x).toAlgebra
    letI := koszulResidueModule a q
    letI := koszulResidueModule z[a,x] q
    (KoszulResidue z[a,x] ⊗[KoszulResidue a] (koszulComplex a).homology q) →ₗ[KoszulResidue z[a,x]]
      (koszulComplex z[a,x]).homology q := by
  letI := (relativeKoszulResidueMap a x).toAlgebra
  letI := koszulResidueModule a q
  letI := koszulResidueModule z[a,x] q
  let f := relativeKoszulHomologyMap a x q
  let M := ModuleCat.of (KoszulResidue a) ((koszulComplex a).homology q)
  let N := ModuleCat.of (KoszulResidue z[a,x]) ((koszulComplex z[a,x]).homology q)
  let N' := (ModuleCat.restrictScalars (relativeKoszulResidueMap a x)).obj N
  let k : M ⟶ N' := by
    letI : Module (KoszulResidue a) N' := N'.isModule
    exact ModuleCat.ofHom (X := ↑M) (Y := ↑N')
      { toFun := fun y ↦ f.hom y
        map_add' := f.hom.map_add
        map_smul' := by
          intro c y
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact f.hom.map_smul b y }
  exact (((ModuleCat.extendRestrictScalarsAdj (relativeKoszulResidueMap a x)).homEquiv M N).symm
    k).hom

/-- 概要：有限列に関する古典環の相対完全正則性。
方針：標的の導来完備性、零次剰余の平坦性、標準比較射の全次数での全単射を課す。
規約：BS 著者版 Definition 2.42。基底の Koszul ホモロジーが非零でも適用できる。
使われ方：prism の (p,d) に関する相対完全正則性。 -/
@[expose] def IsCompletelyRegularRel (a : Fin n → A) (x : Fin r → B) : Prop :=
  letI := (relativeKoszulResidueMap a x).toAlgebra
  (∀ i, IsModuleComplete B (algebraMap A B (a i)) (ModuleCat.of B B)) ∧
    Module.Flat (KoszulResidue a) (KoszulResidue z[a,x]) ∧
    ∀ q : ℤ, Function.Bijective (relativeKoszulComparison a x q)

/-- BS 著者版 Definition 2.42 の (p,d) への特殊化。 -/
@[expose] def IsPrismCompletelyRegularRel {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A)
    (x : Fin r → B) : Prop :=
  IsCompletelyRegularRel ![(p : A), P.generator] x

end SerrePositivity.BhattScholze.Prismatic
