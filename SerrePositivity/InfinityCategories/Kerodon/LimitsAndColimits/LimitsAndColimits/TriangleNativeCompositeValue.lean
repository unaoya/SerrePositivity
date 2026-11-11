module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledNativeTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData

/-!
概要：二短辺を固定した任意の二単体の native Hom の合成端を読む。
方針：面上の辺の射データを元の通常の関手へ戻し、全 path の合成を使う。
規約：対象も依存和に含めて比較し、端点の移送を省略しない。
使われ方：Ind-S (9) の任意の入力二胞体からの長 Hom 全族読出し。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 第一面の二点 path の像。 -/
def triangleFirstNativePath : Path
    (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 1) :=
  (SimplicialThickening.functorMap (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap
    ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath

/-- 第二面の二点 path の像。 -/
def triangleLastNativePath : Path
    (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) :=
  (SimplicialThickening.functorMap (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap
    ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath

/-- 隣接二短辺の path の合成は全 path。 -/
lemma triangleNativePaths_comp :
    ({ I := triangleFirstNativePath.{u}.I ∪ triangleLastNativePath.{u}.I
       left := Or.inl triangleFirstNativePath.left
       right := Or.inr triangleLastNativePath.right
       left_le := fun _ _ => Fin.zero_le _
       le_right := fun _ _ => Fin.le_last _ } : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath := by
  apply SimplicialThickening.Path.ext
  ext ⟨k⟩
  change (ULift.up k ∈ _ ∪ _) ↔ (ULift.up k : ULift.{u} (Fin 3)) ∈ Set.univ
  constructor
  · intro _; trivial
  · intro _
    fin_cases k
    · exact Or.inl ⟨ULift.up (0 : Fin 2), Set.mem_univ _, rfl⟩
    · exact Or.inl ⟨ULift.up (1 : Fin 2), Set.mem_univ _, rfl⟩
    · exact Or.inr ⟨ULift.up (1 : Fin 2), Set.mem_univ _, rfl⟩

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 第一辺の通常の射データを同じ native path で読む。 -/
lemma triangleFirstNativePath_arrowData (t : (SimplicialNerve C) _⦋2⦌) :
    (⟨t.obj ⟨ULift.up 0⟩, t.obj ⟨ULift.up 1⟩,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor t).map triangleFirstNativePath⟩ : Σ X Y : C, X ⟶ Y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData ((SimplicialNerve C).δ (2 : Fin 3) t) := by
  change (⟨_, _, _⟩ : Σ X Y : C, X ⟶ Y) = ⟨_, _, _⟩
  congr 2
  apply (SimplicialCategory.homEquiv' _ _).injective
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex, Equiv.apply_symm_apply]
  rfl

/-- 第二辺の通常の射データを同じ native path で読む。 -/
lemma triangleLastNativePath_arrowData (t : (SimplicialNerve C) _⦋2⦌) :
    (⟨t.obj ⟨ULift.up 1⟩, t.obj ⟨ULift.up 2⟩,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor t).map triangleLastNativePath⟩ : Σ X Y : C, X ⟶ Y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData ((SimplicialNerve C).δ (0 : Fin 3) t) := by
  change (⟨_, _, _⟩ : Σ X Y : C, X ⟶ Y) = ⟨_, _, _⟩
  congr 2
  apply (SimplicialCategory.homEquiv' _ _).injective
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex, Equiv.apply_symm_apply]
  rfl

/-- 両端を含む射データの一致は、同じ合成の射データの一致を与える。 -/
lemma arrowData_comp_of_eq {A B D X Y Z : C} (a : A ⟶ B) (b : B ⟶ D)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (ha : (⟨A, B, a⟩ : Σ X Y : C, X ⟶ Y) = ⟨X, Y, f⟩)
    (hb : (⟨B, D, b⟩ : Σ X Y : C, X ⟶ Y) = ⟨Y, Z, g⟩) :
    (⟨A, D, a ≫ b⟩ : Σ X Y : C, X ⟶ Y) = ⟨X, Z, f ≫ g⟩ := by
  obtain ⟨rfl, ha⟩ := Sigma.mk.inj_iff.mp ha
  obtain ⟨rfl, ha⟩ := Sigma.mk.inj_iff.mp (eq_of_heq ha)
  obtain rfl := eq_of_heq ha
  obtain ⟨_, hb⟩ := Sigma.mk.inj_iff.mp hb
  obtain ⟨rfl, hb⟩ := Sigma.mk.inj_iff.mp (eq_of_heq hb)
  obtain rfl := eq_of_heq hb
  rfl

/-- 全 path の通常の射データは、指定した元の二射の合成そのもの。 -/
lemma triangleFullNativePath_arrowData_of_faces
    (t : (SimplicialNerve C) _⦋2⦌) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (SimplicialNerve C).δ (2 : Fin 3) t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (hg : (SimplicialNerve C).δ (0 : Fin 3) t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge) :
    (⟨t.obj ⟨ULift.up 0⟩, t.obj ⟨ULift.up 2⟩,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor t).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath⟩ : Σ X Y : C, X ⟶ Y) =
      ⟨X, Z, f ≫ g⟩ := by
  have hfirst := (triangleFirstNativePath_arrowData t).trans
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData hf).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow f))
  have hlast := (triangleLastNativePath_arrowData t).trans
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData hg).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow g))
  have h := arrowData_comp_of_eq _ _ f g hfirst hlast
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor t).map triangleFirstNativePath ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor t).map triangleLastNativePath =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor t).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath := by
    rw [← (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor t).map_comp]
    exact congrArg (fun p : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor t).map p) triangleNativePaths_comp
  rw [hp] at h
  exact h

/-- 全 path での豊穣零単体も、両端込みで元の合成射を厳密に表す。 -/
lemma triangleFullNativeValue_of_faces
    (t : (SimplicialNerve C) _⦋2⦌) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (SimplicialNerve C).δ (2 : Fin 3) t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (hg : (SimplicialNerve C).δ (0 : Fin 3) t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge) :
    (⟨t.obj ⟨ULift.up 0⟩, t.obj ⟨ULift.up 2⟩,
      (t.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath)⟩ : Σ A B : C, (SimplicialCategory.sHom A B) _⦋0⦌) =
      ⟨X, Z, SimplicialCategory.homEquiv' X Z (f ≫ g)⟩ := by
  have h := congrArg (fun s : Σ A B : C, A ⟶ B =>
    (⟨s.1, s.2.1, SimplicialCategory.homEquiv' _ _ s.2.2⟩ :
      Σ A B : C, (SimplicialCategory.sHom A B) _⦋0⦌))
    (triangleFullNativePath_arrowData_of_faces t f g hf hg)
  dsimp only at h
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex] at h
  exact h

/-- 固定した二短辺の両端へ移した全 native Hom は、同じ合成端を厳密に回収する。 -/
lemma triangleNativeHom_exists_of_faces
    (t : (SimplicialNerve C) _⦋2⦌) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (SimplicialNerve C).δ (2 : Fin 3) t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (hg : (SimplicialNerve C).δ (0 : Fin 3) t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge) :
    t.obj ⟨ULift.up 0⟩ = X ∧ t.obj ⟨ULift.up 2⟩ = Z ∧
      ∃ m : nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶ SimplicialCategory.sHom X Z,
        HEq (t.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) m ∧
        m.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath) =
          SimplicialCategory.homEquiv' X Z (f ≫ g) := by
  have h := triangleFullNativeValue_of_faces t f g hf hg
  have hX := congrArg Sigma.fst h
  have hZ := congrArg (fun s : Σ A B : C, (SimplicialCategory.sHom A B) _⦋0⦌ => s.2.1) h
  refine ⟨hX, hZ, ?_⟩
  let m : nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶ SimplicialCategory.sHom X Z :=
    t.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hX hZ)
  refine ⟨m, ?_, ?_⟩
  · dsimp only [m]
    generalize t.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ = q
    cases hX
    cases hZ
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  · dsimp only [m]
    cases hX
    cases hZ
    simp only [eqToHom_refl, Category.comp_id]
    exact eq_of_heq (Sigma.mk.inj_iff.mp
      (eq_of_heq (Sigma.mk.inj_iff.mp h).2)).2

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
