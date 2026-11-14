module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.DependentProductPointedSimplex
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations

/-!
概要：任意の小さい Kan 複体の族の積の全基点 π_* と、座標ごとの π_* の全単射。
方針：単射性では RelStruct を座標ごとに束ね、全射性では代表単体の族を束ねる。
規約：零次数と空の族を含む。有限性を仮定しない。
使われ方：BF 1978 §2、HA §1.4.2。任意の小積の Ω 条件。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.SimplicialDependentProduct
end SerrePositivity.KST.Spectra.SimplicialDependentProduct
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type u} (X : S → SSet.{u}) [∀ s, KanComplex (X s)]

/-- 実際の積の射影が誘導する全次数の π の座標表示。 -/
def homotopyMap (n : ℕ) (b : ∀ s, (X s) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.obj S X) n b → ∀ s, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X s) n (b s) :=
  fun a s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S X s) rfl a

/-- 座標の π の全ての族が積の π と一意に対応する。 -/
lemma homotopyMap_bijective (n : ℕ) (b : ∀ s, (X s) _⦋0⦌) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap X n b) := by
  constructor
  · intro a c h
    obtain ⟨f, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
    obtain ⟨g, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n c
    have hs (s : S) : Nonempty (PtSimplex.RelStruct
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S X s) rfl f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S X s) rfl g) 0) := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct n _ _ 0).mp
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk] using congrFun h s
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.DependentProductPointedSimplex.relStruct (fun s ↦ Classical.choice (hs s)))
  · intro a
    choose f hf using fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n (a s)
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.DependentProductPointedSimplex.simplex f), ?_⟩
    funext s
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S X s) rfl _ = a s
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.DependentProductPointedSimplex.eval_simplex, hf]

/-- 族の射を積の射へ束ねる。 -/
def map {Y : S → SSet.{u}} (f : ∀ s, X s ⟶ Y s) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.obj S X ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.obj S Y :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift (fun s ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S X s ≫ f s)

omit [∀ s, KanComplex (X s)] in
@[reassoc (attr := simp)]
lemma map_eval {Y : S → SSet.{u}} (f : ∀ s, X s ⟶ Y s) (s : S) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map X f ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S Y s = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S X s ≫ f s := rfl

/-- 座標表示は族の射に関して自然。 -/
lemma homotopyMap_naturality {Y : S → SSet.{u}} [∀ s, KanComplex (Y s)]
    (f : ∀ s, X s ⟶ Y s) (n : ℕ) (b : ∀ s, (X s) _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.obj S X) n b) (s : S) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap Y n (fun s ↦ (f s).app _ (b s))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map X f) rfl a) s =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f s) rfl (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap X n b a s) := by
  obtain ⟨t, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk]
  rfl

/-- 全基点 π 同型の任意の小積も全基点 π 同型。 -/
lemma map_piIsomorphism {Y : S → SSet.{u}} [∀ s, KanComplex (Y s)]
    (f : ∀ s, X s ⟶ Y s) (hf : ∀ s, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f s)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map X f) := by
  intro b n
  have h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap Y n (fun s ↦ (f s).app _ (b s)) ∘
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map X f) rfl =
      (fun a s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f s) rfl (a s)) ∘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap X n b := by
    funext a s
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap_naturality X f n b a s
  have hpi : Function.Bijective
      (fun a : ∀ s, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X s) n (b s) ↦
        fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f s) rfl (a s)) := by
    constructor
    · intro a c hac
      funext s
      exact (hf s (b s) n).injective (congrFun hac s)
    · intro a
      choose c hc using fun s ↦ (hf s (b s) n).surjective (a s)
      exact ⟨c, funext hc⟩
  have hc := hpi.comp (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap_bijective X n b)
  rw [← h] at hc
  exact hc.of_comp_left (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap_bijective Y n _).injective

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct.homotopyMap := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct.homotopyMap_bijective := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap_bijective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct.homotopyMap_naturality := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap_naturality

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct.map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct.map_eval := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map_eval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct.map_eval_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map_eval_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct.map_piIsomorphism := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map_piIsomorphism

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct.homotopyMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct.homotopyMap.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.homotopyMap.eq_1
