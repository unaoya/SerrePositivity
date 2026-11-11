module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan
public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal

/-!
概要：core の構成の積との整合性。
方針：辺の外積の可逆性をホモトピー圏の積比較で示し、積の射を core に持ち上げる。
規約：積は単体集合の cartesian monoidal 構造で表す。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、Remark 5.5.3.9（Tag 05Q1） の豊穣合成の準備。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：可逆な二つの一単体の組は積の中でも可逆。
方針：二切断のホモトピー圏の積比較の逆関手で同型の組を写す。
規約：quasicategory 性を仮定せず、生成されたホモトピー圏で証明する。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、core の積からの射の構成。 -/
lemma isInvertibleEdge_pair {X Y : SSet.{u}} (e : X _⦋1⦌) (f : Y _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e)) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X := X ⊗ Y) (e, f)) := by
  have := he
  have := hf
  let F := SSet.Truncated.HomotopyCategory.BinaryProduct.inverse
    ((truncation 2).obj X) ((truncation 2).obj Y)
  have hp : IsIso (CategoryTheory.Prod.mkHom
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e))
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex f))) :=
    (isIso_prod_iff _ _).mpr ⟨he, hf⟩
  have h : IsIso (F.map (CategoryTheory.Prod.mkHom
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e))
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex f)))) := by infer_instance
  rw [SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_map_mkHom_homMk_homMk] at h
  exact h

/-- 概要：二つの core の積から積の core への標準射。
方針：二つの包含の積が全ての辺を可逆な辺へ写すことを使う。
規約：各次数では二つの部分型の値を組にする。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、core の Hom の豊穣合成。 -/
def quasicategoryCoreProduct (X Y : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (X ⊗ Y) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι)
    (fun s ↦ isInvertibleEdge_pair s.1.val s.2.val
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge s.1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge s.2))

/-- 概要：単体集合のモノイダル単位からその core への射。
方針：単位の各次数が一点であることから全ての辺を退化辺として扱う。
規約：包含との合成は単位の恒等射。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、豊穣圏の恒等射。 -/
def quasicategoryCoreUnit : (𝟙_ SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (𝟙_ SSet.{u}) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift (𝟙 _) (fun s ↦ by
    let v := (𝟙_ SSet.{u}).δ 0 s
    have hs : s = (𝟙_ SSet.{u}).σ 0 v := by
      change (s : PUnit) = _
      exact @Subsingleton.elim PUnit inferInstance s _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((𝟙_ SSet.{u}).σ 0 v)) hs).mpr
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_degenerate v))

/-- 概要：core の構成は積に関する lax monoidal 関手。
方針：積と単位の射を部分型の値で計算し、自然性・結合律・単位律を確認する。
規約：比較射は元の単体の組を変えない。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、core による豊穣構造の移送。 -/
instance quasicategoryCoreFunctor_laxMonoidal : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u}.LaxMonoidal where
  ε := quasicategoryCoreUnit
  μ X Y := quasicategoryCoreProduct X Y
  μ_natural_left f X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl
  μ_natural_right X f := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl
  associativity X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl
  left_unitality X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl
  right_unitality X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl

/-- 概要：単位からの射は core への単位からの射と一対一に対応する。
方針：両者を零単体で表示し、core が全頂点を含むことを使う。
規約：同値の逆は core の包含への後合成に対応する。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、通常の射を保つ豊穣構造の移送。 -/
def quasicategoryCoreUnitHomEquiv (X : SSet.{u}) :
    ((𝟙_ SSet.{u}) ⟶ X) ≃ ((𝟙_ SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u})) :=
  (SSet.unitHomEquiv X).trans
    (({ toFun := fun x ↦ ⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex x⟩
        invFun := Subtype.val
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl } :
      X _⦋0⦌ ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) _⦋0⦌).trans
        (SSet.unitHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u})).symm)

/-- 概要：単位からの射の同値は core 関手の lax monoidal 構造による標準写像。
方針：零単体で評価し、部分型の値を比較する。
規約：ε の後に core の射を合成する。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、通常の圏構造と豊穣構造の整合性。 -/
lemma quasicategoryCoreUnitHomEquiv_eq (X : SSet.{u}) (f : (𝟙_ SSet.{u}) ⟶ X) :
    quasicategoryCoreUnitHomEquiv X f = quasicategoryCoreUnit ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap f := by
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  simp only [quasicategoryCoreUnitHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
