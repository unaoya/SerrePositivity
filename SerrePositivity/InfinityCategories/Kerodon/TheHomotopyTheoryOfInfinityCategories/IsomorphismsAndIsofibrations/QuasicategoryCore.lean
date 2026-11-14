module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：可逆な辺だけを持つ単体の core 部分複体。
方針：各単体の全ての一次単体への制限に可逆性を課す。
規約：部分複体の定義と関手性は任意の単体集合で与え、Kan 性は別に示す。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、Construction 5.5.3.1（Tag 0209） の関手単体集合の core。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：全ての辺が可逆な単体からなる部分複体。
方針：標準一単体からの全ての射で制限した辺の可逆性を要求する。
規約：退化した辺への制限も含める。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、quasicategory の core の定義。 -/
@[kerodon 01D0]
def quasicategoryCore (X : SSet.{u}) : X.Subcomplex where
  obj n := {s | ∀ f : ⦋1⦌ ⟶ n.unop, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.map f.op s))}
  map {n m} g s hs := by
    intro f
    have h := hs (f ≫ g.unop)
    rw [op_comp, Quiver.Hom.op_unop, X.map_comp] at h
    exact h

/-- 概要：core の一単体を周囲の単体集合で見ると可逆。
方針：定義中の制限を標準一単体の恒等射に取る。
規約：可逆性は周囲のホモトピー圏で測る。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、core への射の持ち上げと関手性。 -/
lemma quasicategoryCore_edge {X : SSet.{u}} (s : (quasicategoryCore X : SSet.{u}) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s.val) := by
  have h := s.property (𝟙 ⦋1⦌)
  rw [op_id, X.map_id] at h
  exact h

/-- 概要：全ての辺を可逆な辺に写す射は core に持ち上がる。
方針：自然性によって各単体の辺の制限を元の射の一次成分に移す。
規約：頂点ごとの条件だけには弱めず、全ての一単体を量化する。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、core の普遍的な部分複体への持ち上げ。 -/
@[kerodon 01D8]
def quasicategoryCoreLift {A X : SSet.{u}} (f : A ⟶ X)
    (hf : ∀ s : A _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s))) :
    A ⟶ (quasicategoryCore X : SSet.{u}) :=
  Subcomplex.lift f (by
    intro n s hs
    obtain ⟨s, rfl⟩ := hs
    intro g
    rw [← CategoryTheory.NatTrans.naturality_apply]
    exact hf (A.map g.op s))

/-- 概要：core への持ち上げを含めると元の射。
方針：部分複体への持ち上げの定義を展開する。
規約：可逆性の証明の選択によらない。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、core の関手則の比較。 -/
lemma quasicategoryCoreLift_ι {A X : SSet.{u}} (f : A ⟶ X)
    (hf : ∀ s : A _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s))) :
    quasicategoryCoreLift f hf ≫ (quasicategoryCore X).ι = f := rfl

/-- 概要：単体集合の射は core の間の射を誘導する。
方針：単体集合の射がホモトピー圏の同型を保つことを使う。
規約：始域・終域の quasicategory 性は関手性の定義には不要。
使われ方：Kerodon Remark 5.5.3.9（Tag 05Q1）、core の関手性。 -/
def quasicategoryCoreMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    (quasicategoryCore X : SSet.{u}) ⟶ (quasicategoryCore Y : SSet.{u}) :=
  quasicategoryCoreLift ((quasicategoryCore X).ι ≫ f) (fun s ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s.val).map ((truncation 2).map f))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s.val)) rfl).mp
        ((quasicategoryCore_edge s).map f))

/-- 概要：core の射と周囲への包含は可換。
方針：部分複体への持ち上げの包含との合成を計算する。
規約：f は任意の単体集合の射。
使われ方：Kerodon Remark 5.5.3.9（Tag 05Q1）、core の関手則。 -/
lemma quasicategoryCoreMap_ι {X Y : SSet.{u}} (f : X ⟶ Y) :
    quasicategoryCoreMap f ≫ (quasicategoryCore Y).ι = (quasicategoryCore X).ι ≫ f := rfl

/-- 概要：core の構成は単体集合の圏上の関手。
方針：包含の単射性で恒等と合成の式を反映する。
規約：この段階では値が Kan 複体であるとは主張しない。
使われ方：Kerodon Remark 5.5.3.9（Tag 05Q1）、Kan な豊穣 Hom の合成の準備。 -/
@[kerodon 01D0]
def quasicategoryCoreFunctor : SSet.{u} ⥤ SSet.{u} where
  obj X := (quasicategoryCore X : SSet.{u})
  map f := quasicategoryCoreMap f
  map_id X := by
    apply (cancel_mono (quasicategoryCore X).ι).1
    rw [quasicategoryCoreMap_ι, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (quasicategoryCore _).ι).1
    simp only [Category.assoc, quasicategoryCoreMap_ι]
    rw [← Category.assoc (quasicategoryCoreMap f) (quasicategoryCore _).ι g,
      quasicategoryCoreMap_ι, Category.assoc]

/-- 概要：退化した一単体はホモトピー圏で可逆。
方針：端点付き恒等辺の生成射が恒等射であることを使う。
規約：標的の quasicategory 性は不要。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、core の全頂点と退化辺。 -/
lemma isInvertibleEdge_degenerate {X : SSet.{u}} (v : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.σ 0 v)) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj X) v) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) v))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.σ 0 v)) (f := SSet.Truncated.Edge.id (X := (truncation 2).obj X) v) rfl).mpr h

/-- 概要：core は周囲の単体集合の全ての頂点を含む。
方針：零単体の一次制限は退化辺であることを使う。
規約：零単体の式自体を変更しない。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、core と周囲の対象の一致。 -/
lemma quasicategoryCore_vertex {X : SSet.{u}} (v : X _⦋0⦌) :
    v ∈ (quasicategoryCore X).obj (Opposite.op ⦋0⦌) := by
  intro f
  have hf : f = SimplexCategory.σ (0 : Fin 1) := Subsingleton.elim _ _
  rw [hf]
  exact isInvertibleEdge_degenerate v

/-- 概要：標準区間の自己射は二つの定値射か恒等射。
方針：二点順序集合の単調自己写像を有限に判定する。
規約：標準区間の向きを保つ単体圏の射だけを扱う。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、core の一単体の特徴づけ。 -/
lemma intervalEndomorphism_cases (f : ⦋1⦌ ⟶ ⦋1⦌) :
    f = SimplexCategory.const _ _ 0 ∨ f = 𝟙 _ ∨ f = SimplexCategory.const _ _ 1 := by
  have h : ∀ F : Fin 2 → Fin 2, Monotone F →
      F = (fun _ ↦ 0) ∨ F = id ∨ F = (fun _ ↦ 1) := by decide
  rcases h f.toOrderHom f.toOrderHom.monotone with h | h | h
  · left
    apply SimplexCategory.Hom.ext
    ext i
    exact congrArg Fin.val (congrFun h i)
  · right; left
    apply SimplexCategory.Hom.ext
    ext i
    exact congrArg Fin.val (congrFun h i)
  · right; right
    apply SimplexCategory.Hom.ext
    ext i
    exact congrArg Fin.val (congrFun h i)

/-- 概要：core の一単体は周囲で可逆な一単体と一致。
方針：標準区間の自己射を恒等と二つの定値に分ける。
規約：可逆性は端点を面で定めた辺に課す。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、core の辺の正確な特徴づけ。 -/
@[kerodon 01D0]
lemma quasicategoryCore_mem_edge_iff {X : SSet.{u}} (s : X _⦋1⦌) :
    s ∈ (quasicategoryCore X).obj (Opposite.op ⦋1⦌) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s) := by
  constructor
  · intro hs
    exact quasicategoryCore_edge ⟨s, hs⟩
  · intro hs f
    rcases intervalEndomorphism_cases f with hf | hf | hf
    · have hc : SimplexCategory.const ⦋1⦌ ⦋1⦌ 0 =
          SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by decide
      rw [hf, hc, op_comp, X.map_comp]
      exact isInvertibleEdge_degenerate (X.δ 1 s)
    · rw [hf, op_id, X.map_id]
      exact hs
    · have hc : SimplexCategory.const ⦋1⦌ ⦋1⦌ 1 =
          SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (0 : Fin 2) := by decide
      rw [hf, hc, op_comp, X.map_comp]
      exact isInvertibleEdge_degenerate (X.δ 0 s)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.5.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
attribute [cite HTT "1.2.5.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift
