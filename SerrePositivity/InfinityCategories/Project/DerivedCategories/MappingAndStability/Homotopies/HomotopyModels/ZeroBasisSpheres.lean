module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.Semifree
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # 微分零の自由複体の sphere 余積表示

概要：各次数に基底を持つ微分零の複体を自由 sphere の余積として表示する。
方針：基底元を cycle として sphere から写し、基底による線形延長で余積普遍性を示す。
規約：基底の添字に有限性を課さない。使われ方：semifree filtration の初期段と商。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex MonoidalCategory
variable (S : Type u) [CommRing S]

/-- 概要：sphere の生成元の像は複体の射との合成に関して自然である。
方針：唯一の次数で生成元の像を評価する。
規約：生成元の値は cycle の underlying 要素。使われ方：sphere 余積の普遍性。 -/
theorem sphereCycle_comp {P Q : Complex S} (k : ℤ)
    (f : complexSphere S k ⟶ P) (g : P ⟶ Q) :
    (complexSphereHomEquiv S Q k (f ≫ g)).val =
      (g.f k) (complexSphereHomEquiv S P k f).val := by
  change (((singleObjXSelf (.up ℤ) k (𝟙_ (ModuleCat S))).inv ≫
    (f ≫ g).f k) (1 : S)) = _
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  rfl

variable {P : Complex S} {I : ℤ → Type u}
  (E : ∀ k, Module.Basis (I k) S (P.X k))
  (hz : ∀ k : ℤ, P.d k (k + 1) = 0)

/-- 概要：各基底元からの sphere の写像を集めた cofan。
方針：微分零の仮定により各基底元を cycle とみなす。
規約：全次数の基底を直和型で添字付ける。使われ方：自由 sphere 表示。 -/
def zeroBasisSphereCofan : Cofan (fun a : Σ k, I k => complexSphere S a.1) :=
  Cofan.mk P (fun a => (complexSphereHomEquiv S P a.1).symm
    ⟨E a.1 a.2, by change (P.d a.1 (a.1 + 1)) (E a.1 a.2) = 0; rw [hz]; rfl⟩)

/-- 概要：sphere の cofan から元の複体を始域とする比較射を構成する。
方針：各 sphere の生成元の像を基底上で指定し線形延長する。
規約：値は sphere の cycle の underlying 要素。使われ方：余積の普遍性。 -/
def zeroBasisSphereDesc (c : Cofan (fun a : Σ k, I k => complexSphere S a.1)) :
    P ⟶ c.pt :=
  CochainComplex.ofHom
    (fun k => ModuleCat.ofHom ((E k).constr S (fun i =>
      (complexSphereHomEquiv S c.pt k (c.inj ⟨k, i⟩)).val))) (by
      intro k
      rw [hz, zero_comp]
      apply ModuleCat.hom_ext
      apply (E k).ext
      intro i
      change (c.pt.d k (k + 1))
        (((E k).constr S (fun i =>
          (complexSphereHomEquiv S c.pt k (c.inj ⟨k, i⟩)).val)) (E k i)) = 0
      rw [Module.Basis.constr_basis]
      exact (complexSphereHomEquiv S c.pt k (c.inj ⟨k, i⟩)).property)

/-- 概要：比較射は生成元の各 sphere 上で指定された射に一致する。
方針：sphere からの射を cycle の像で判定し、基底上の線形延長を評価する。
規約：各次数と基底元を同時に扱う。使われ方：cofan の余積性。 -/
theorem zeroBasisSphereDesc_fac
    (c : Cofan (fun a : Σ k, I k => complexSphere S a.1)) (a : Σ k, I k) :
    (zeroBasisSphereCofan S E hz).inj a ≫ zeroBasisSphereDesc S E hz c = c.inj a := by
  apply (complexSphereHomEquiv S c.pt a.1).injective
  apply Subtype.ext
  rw [sphereCycle_comp]
  have he := congrArg Subtype.val ((complexSphereHomEquiv S P a.1).apply_symm_apply
    ⟨E a.1 a.2, by change (P.d a.1 (a.1 + 1)) (E a.1 a.2) = 0; rw [hz]; rfl⟩)
  change (zeroBasisSphereDesc S E hz c).f a.1
    (complexSphereHomEquiv S P a.1
      ((complexSphereHomEquiv S P a.1).symm
        ⟨E a.1 a.2, by change (P.d a.1 (a.1 + 1)) (E a.1 a.2) = 0; rw [hz]; rfl⟩)).val = _
  rw [he]
  exact (E a.1).constr_basis S _ a.2

/-- 概要：各次数に基底を持つ微分零の複体は sphere の余積である。
方針：比較射の存在と、基底元上の値による一意性を示す。
規約：基底は無限でもよい。使われ方：初期段と自由商の実際の余積表示。 -/
def zeroBasisSphereIsColimit : IsColimit (zeroBasisSphereCofan S E hz) := by
  refine Cofan.IsColimit.mk _ (zeroBasisSphereDesc S E hz)
    (zeroBasisSphereDesc_fac S E hz) ?_
  intro c m h
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply (E k).ext
  intro i
  have hi := congrArg (fun f => (complexSphereHomEquiv S c.pt k f).val) (h ⟨k, i⟩)
  rw [sphereCycle_comp] at hi
  have he := congrArg Subtype.val ((complexSphereHomEquiv S P k).apply_symm_apply
    ⟨E k i, by change (P.d k (k + 1)) (E k i) = 0; rw [hz]; rfl⟩)
  change (m.f k) (complexSphereHomEquiv S P k
    ((complexSphereHomEquiv S P k).symm
      ⟨E k i, by change (P.d k (k + 1)) (E k i) = 0; rw [hz]; rfl⟩)).val = _ at hi
  rw [he] at hi
  change (m.f k) (E k i) = _
  exact hi.trans ((E k).constr_basis S
    (fun j => (complexSphereHomEquiv S c.pt k (c.inj ⟨k, j⟩)).val) i).symm

/-- 概要：微分零の次数ごとの自由複体と通常の sphere の余積の同型。
方針：上で示した余極限と選択された余積の一意同型を使う。
規約：向きは元の複体から余積。使われ方：一点 dg 加群への表示の転送。 -/
def zeroBasisSphereIso : P ≅ ∐ (fun a : Σ k, I k => complexSphere S a.1) :=
  (zeroBasisSphereIsColimit S E hz).coconePointUniqueUpToIso (colimit.isColimit _)

/-- 概要：微分零の次数ごとの自由複体の一点加群は自由 sphere 表示を持つ。
方針：評価の余積保存と自由 sphere の評価同型で通常の表示を戻す。
規約：正本は既存の `ModuleSphereFreePresentation`。使われ方：semifree filtration の構成。 -/
def zeroBasisModuleSpherePresentation :
    ModuleSphereFreePresentation S PUnit.{1}
      (ForgetEnrichment.of (Complex S) (ringModule S P)) where
  Index := Σ k, I k
  object _ := PUnit.unit
  degree a := a.1
  iso := (moduleEvaluation S PUnit.{1} PUnit.unit).preimageIso
    (zeroBasisSphereIso S E hz ≪≫
      (Limits.Sigma.mapIso (fun a : Σ k, I k => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.freeSphereEvaluationIso S a.1)).symm ≪≫
      (PreservesCoproduct.iso (ringModuleEquivalence S).functor
        (fun a : Σ k, I k => freeSphere S PUnit.{1} PUnit.unit a.1)).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
