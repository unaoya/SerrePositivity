module


public meta import SerrePositivity.Util.Citation
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Category.TopCat.Basic

/-! # The actual homotopy maps used in geometric weak equivalences

Weak equivalence requires a bijection of path components and a bijection
on every positive homotopy group at every source point. The separate
component condition also covers an empty source. No model structure is assumed.
-/

@[expose] public section
universe u
open CategoryTheory
namespace SerrePositivity.TopologicalHomotopy
variable {X Y Z : TopCat.{u}}

/-- Postcomposition on loops relative to the entire cube boundary. -/
def loopMap (f : X ⟶ Y) (x : X) (n : ℕ) :
    GenLoop (Fin n) X x → GenLoop (Fin n) Y (f x) :=
  fun p ↦ ⟨f.hom.comp p.1, fun t ht ↦ congrArg f (p.2 t ht)⟩

/-- The map of homotopy classes induced by the given continuous map. -/
def homotopyMap (f : X ⟶ Y) (x : X) (n : ℕ) :
    HomotopyGroup (Fin n) X x → HomotopyGroup (Fin n) Y (f x) :=
  Quotient.map (loopMap f x n) (fun _ _ h ↦ h.comp_continuousMap f.hom)

/-- The actual induced map of path components. -/
def componentMap (f : X ⟶ Y) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x ↦ ZerothHomotopy.mk (f x))
    (fun _ _ p ↦ ZerothHomotopy.sound (p.map f.hom.continuous))

@[simp] lemma componentMap_mk (f : X ⟶ Y) (x : X) :
    componentMap f (ZerothHomotopy.mk x) = ZerothHomotopy.mk (f x) := rfl

@[simp] lemma componentMap_id : componentMap (𝟙 X) = id := by
  funext a
  induction a using ZerothHomotopy.rec
  rfl

@[simp] lemma componentMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    componentMap (f ≫ g) = componentMap g ∘ componentMap f := by
  funext a
  induction a using ZerothHomotopy.rec
  rfl

@[simp] lemma homotopyMap_id (x : X) (n : ℕ) : homotopyMap (𝟙 X) x n = id := by
  funext a
  induction a using Quotient.inductionOn
  rfl

@[simp] lemma homotopyMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (n : ℕ) :
    homotopyMap (f ≫ g) x n = homotopyMap g (f x) n ∘ homotopyMap f x n := by
  funext a
  induction a using Quotient.inductionOn
  rfl

/-- Geometric weak homotopy equivalences, with every component and basepoint tested. -/
def weakHomotopyEquivalences : MorphismProperty TopCat.{u} := fun X _ f ↦
  Function.Bijective (componentMap f) ∧
    ∀ (x : X) (n : ℕ), Function.Bijective (homotopyMap f x (n + 1))

lemma weakHomotopyEquivalences_id (X : TopCat.{u}) : weakHomotopyEquivalences (𝟙 X) := by
  constructor
  · simpa using Function.bijective_id
  · intro x n
    simpa using Function.bijective_id

lemma weakHomotopyEquivalences_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : weakHomotopyEquivalences f) (hg : weakHomotopyEquivalences g) :
    weakHomotopyEquivalences (f ≫ g) := by
  constructor
  · rw [componentMap_comp]
    exact hg.1.comp hf.1
  · intro x n
    rw [homotopyMap_comp]
    exact (hg.2 (f x) n).comp (hf.2 x n)

end SerrePositivity.TopologicalHomotopy

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.1.3.4"] _root_.SerrePositivity.TopologicalHomotopy.weakHomotopyEquivalences
attribute [cite HTT "1.1.3.6" (partial := component) "仮定：位相豊穣関手 F の各 Hom に誘導される連続写像を入力（HTT の各 Hom の条件と一致）。結論：weakHomotopyEquivalences は π0 と全基点・正次数 πn の全単射を要求するので、明記された第一条件の弱ホモトピー同値の判定を表す。F 全体の hF の本質的全射を組み合わせた定義と hC との比較はない。"] _root_.SerrePositivity.TopologicalHomotopy.weakHomotopyEquivalences
