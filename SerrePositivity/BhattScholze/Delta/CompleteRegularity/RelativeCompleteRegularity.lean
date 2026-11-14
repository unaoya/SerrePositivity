module
public import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Basic

public import SerrePositivity.HomologicalAlgebra.KoszulAlgebraTorComparison
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# 有限列に関する相対完全正則性

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
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

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Def 2.42" (partial := special) "Koszul ホモロジーによる比較（D20）の古典的な環の版（BS-W15 K3） ／ 11-11 更新 ／ 11-12 夜更新（ノート本文の更新時） ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.IsCompletelyRegularRel
attribute [cite BS19 "Def 2.42" (partial := special) "Koszul ホモロジーによる比較（D20）の古典的な環の版（BS-W15 K3） ／ 11-11 更新 ／ 11-12 夜更新（ノート本文の更新時） ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.relativeKoszulComparison
attribute [cite HA "7.2.2.10" (partial := stronger-hyp) "仮定：通常の可換環 A→B と二つの有限列から作る Koszul の標準射（Lean が強い：指定 Koszul 模型に限り、標的の各基底座標に関する導来完備性も要求する）。結論：零次の剰余環の平坦性と、全整数余鎖次数 q での標準射 H^q(基底)⊗H⁰(標的)→H^q(標的) の全単射を定義の条件とする（この指定射について HA の二条件に一致する部分）。テンソルの順序は可換環の対称性で交換する。一般の E₁ 環加群の flat 述語と Koszul の環スペクトル模型との比較は含まれない。高次ホモロジーの消滅を要求する定義ではない。"] _root_.SerrePositivity.BhattScholze.Prismatic.IsCompletelyRegularRel
attribute [cite HA "7.2.2.10" (partial := stronger-hyp) "仮定：通常の可換環 A→B と二つの有限列から作る Koszul の標準射（Lean が強い：指定 Koszul 模型に限り、標的の各基底座標に関する導来完備性も要求する）。結論：零次の剰余環の平坦性と、全整数余鎖次数 q での標準射 H^q(基底)⊗H⁰(標的)→H^q(標的) の全単射を定義の条件とする（この指定射について HA の二条件に一致する部分）。テンソルの順序は可換環の対称性で交換する。一般の E₁ 環加群の flat 述語と Koszul の環スペクトル模型との比較は含まれない。高次ホモロジーの消滅を要求する定義ではない。"] _root_.SerrePositivity.BhattScholze.Prismatic.relativeKoszulComparison
