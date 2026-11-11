module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeBasis

/-! # 高さで切った部分複体の余極限

概要：semibasis の高さによる部分複体の余極限は元の複体である。
方針：各基底元をそれが属する段から写し、基底による線形延長を用いる。
規約：有限性は基底展開の台だけに用いる。使われ方：semifree filtration の網羅性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits
open _root_.SerrePositivity.DifferentialGraded
variable {S : Type u} [CommRing S] {P : Complex S} (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P)

/-- 概要：高さが上限以下の基底元はその段に属する。
方針：線形包の生成元としての所属。規約：上限を含む。
使われ方：余極限の射を基底元上で定義する。 -/
theorem basis_mem_stage (k : ℤ) (i : B.Index k) (n : ℕ) (h : B.height k i ≤ n) :
    B.basis k i ∈ B.stageSubmodule n k :=
  Submodule.subset_span ⟨i, h, rfl⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (basis_mem_stage)


/-- 概要：cocone から基底の線形延長で定める各次数の比較写像。
方針：基底元をその高さの段の写像で送る。規約：係数環に追加仮定はない。
使われ方：余極限からの複体の射の成分。 -/
def colimitComponent (c : Cocone B.stageDiagram) (k : ℤ) : P.X k →ₗ[S] c.pt.X k :=
  (B.basis k).constr S (fun i =>
    (c.ι.app (B.height k i)).f k
      ⟨B.basis k i, B.basis_mem_stage k i _ le_rfl⟩)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (colimitComponent)


private theorem ComplexSemifreeBasis.colimitComponent_fac (c : Cocone B.stageDiagram) (n : ℕ) (k : ℤ)
    (x : P.X k) (hx : x ∈ B.stageSubmodule n k) :
    B.colimitComponent c k x = (c.ι.app n).f k ⟨x, hx⟩ := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [colimitComponent, Module.Basis.constr_basis]
    have h := congrArg (fun f => f.f k
      ⟨B.basis k i, B.basis_mem_stage k i _ le_rfl⟩)
      (c.w (homOfLE hi))
    change (c.ι.app n).f k ⟨B.basis k i, B.basis_mem_stage k i n hi⟩ =
      (c.ι.app (B.height k i)).f k
        ⟨B.basis k i, B.basis_mem_stage k i _ le_rfl⟩ at h
    exact h.symm
  | zero =>
    change _ = (c.ι.app n).f k 0
    simp only [map_zero]
  | add x y hx hy ihx ihy =>
    change B.colimitComponent c k (x + y) =
      (c.ι.app n).f k (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | smul a x hx ih =>
    change B.colimitComponent c k (a • x) = (c.ι.app n).f k (a • ⟨x, hx⟩)
    rw [map_smul, map_smul, ih]

/-- 概要：基底から延長した比較写像は微分と可換する。
方針：要素を含む段を選び、その段の複体の射の可換性に帰着する。
規約：任意の非有界複体。使われ方：比較射の複体の射としての構成。 -/
theorem colimitComponent_comm (c : Cocone B.stageDiagram) (k : ℤ) :
    ModuleCat.ofHom (B.colimitComponent c k) ≫ c.pt.d k (k + 1) =
      P.d k (k + 1) ≫ ModuleCat.ofHom (B.colimitComponent c (k + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨n, hx⟩ := B.exists_mem_stageSubmodule k x
  change (c.pt.d k (k + 1)) (B.colimitComponent c k x) =
    B.colimitComponent c (k + 1) ((P.d k (k + 1)) x)
  rw [B.colimitComponent_fac c n k x hx,
    B.colimitComponent_fac c n (k + 1) _ (B.differential_mem_stage n k hx)]
  have h := congrArg (fun f => f.hom ⟨x, hx⟩) ((c.ι.app n).comm k (k + 1))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis.stageDiagram, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis.stageComplex] at h
  rw [CochainComplex.of_d] at h
  exact h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (colimitComponent_comm)


/-- 概要：任意の cocone から元の複体を始域とする比較射を作る。
方針：各基底元をその高さの段から写して線形延長し、微分との可換性を示す。
規約：射は実際の複体の射。使われ方：高さの filtration の余極限の普遍性。 -/
def stageColimitDesc (c : Cocone B.stageDiagram) : P ⟶ c.pt :=
  CochainComplex.ofHom (fun k => ModuleCat.ofHom (B.colimitComponent c k))
    (B.colimitComponent_comm c)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (stageColimitDesc)


/-- 概要：余極限候補の比較射は各段で指定された cocone の射に一致する。
方針：部分加群の生成元から線形性で延長した式を使う。
規約：任意の段を許す。使われ方：余極限の分解則。 -/
theorem stageColimitDesc_fac (c : Cocone B.stageDiagram) (n : ℕ) :
    B.stageInclusion n ≫ B.stageColimitDesc c = c.ι.app n := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact B.colimitComponent_fac c n k x.val x.property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (stageColimitDesc_fac)


/-- 概要：高さで切った部分複体の cocone は余極限である。
方針：各基底元の属する段で比較射の値が一意に決まることを使う。
規約：頂点は元の複体そのもの。使われ方：既存 semifree filtration の再構成。 -/
def stageCoconeIsColimit : IsColimit B.stageCocone where
  desc := B.stageColimitDesc
  fac := B.stageColimitDesc_fac
  uniq c m h := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply (B.basis k).ext
    intro i
    have hi := congrArg (fun f => f.f k
      ⟨B.basis k i, B.basis_mem_stage k i _ le_rfl⟩) (h (B.height k i))
    change m.f k (B.basis k i) =
      (c.ι.app (B.height k i)).f k
        ⟨B.basis k i, B.basis_mem_stage k i _ le_rfl⟩ at hi
    change m.f k (B.basis k i) = B.colimitComponent c k (B.basis k i)
    rw [colimitComponent, Module.Basis.constr_basis]
    exact hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (stageCoconeIsColimit)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
