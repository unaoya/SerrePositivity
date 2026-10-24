module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PinchedActionEquivalences
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFamilyComparisonBijective
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantHomFaithful

/-!
概要：指定辺集合に対する局所対象と写像空間の局所性の基本性質。
方針：pinched 模型と区間模型を比較し、任意パラメータの Hom の全単射を得る。
規約：反射や presentable 性は仮定しない。使われ方：HTT 5.5.4.1・5.5.4.2。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 指定した hX の射による前合成が写像空間の同値であるという局所性。 -/
def IsLocalForHom {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (z : X _⦋0⦌) : Prop := IsQCatEquivalence (PinchedInterval.precompose z f)

/-- 局所性は pinched 模型と区間模型で同値。 -/
lemma isLocalForHom_iff_interval {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (z : X _⦋0⦌) : IsLocalForHom f z ↔ IsQCatEquivalence (intervalPrecompose z f) := by
  let e := PinchedInterval.liftMapComparisonIso (intervalPrecompose z f)
  constructor
  · intro h
    exact (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence y z).cancel_left
      ((h.comp (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence x z)).ofFunctorIso e)
  · intro h
    exact (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence x z).cancel_right
      (((SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence y z).comp h).ofFunctorIso e.symm)

/-- 同型に対して全ての対象が局所。 -/
lemma isLocalForHom_of_isIso {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    [IsIso f] (z : X _⦋0⦌) : IsLocalForHom f z :=
  pinchedPrecompose_isQCatEquivalence_of_isIso f z

/-- 固定対象に対する局所性は射の合成で閉じる。 -/
lemma isLocalForHom_comp {x y z : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (g : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk z)
    (t : X _⦋0⦌) (hf : IsLocalForHom f t) (hg : IsLocalForHom g t) :
    IsLocalForHom (f ≫ g) t :=
  (hg.comp hf).ofFunctorIso (PinchedInterval.precomposeCompIso t f g)

/-- 局所性の二つから三つ目：左因子と合成から右因子。 -/
lemma isLocalForHom_cancel_left {x y z : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (g : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk z)
    (t : X _⦋0⦌) (hf : IsLocalForHom f t) (hfg : IsLocalForHom (f ≫ g) t) :
    IsLocalForHom g t :=
  hf.cancel_right (hfg.ofFunctorIso (PinchedInterval.precomposeCompIso t f g).symm)

/-- 局所性の二つから三つ目：右因子と合成から左因子。 -/
lemma isLocalForHom_cancel_right {x y z : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (g : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk z)
    (t : X _⦋0⦌) (hg : IsLocalForHom g t) (hfg : IsLocalForHom (f ≫ g) t) :
    IsLocalForHom f t :=
  hg.cancel_left (hfg.ofFunctorIso (PinchedInterval.precomposeCompIso t f g).symm)

/-- 局所性は標的対象の同型で不変。 -/
lemma isLocalForHom_iff_of_vertexIso {x y z z' : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (e : VertexIso z z') : IsLocalForHom f z ↔ IsLocalForHom f z' := by
  have hx := pinchedPostcompose_isQCatEquivalence_of_isIso e.hom x
  have hy := pinchedPostcompose_isQCatEquivalence_of_isIso e.hom y
  have h := PinchedInterval.precomposePostcomposeIso f e.hom
  constructor
  · intro hf
    exact hy.cancel_left ((hf.comp hx).ofFunctorIso h)
  · intro hf
    exact hx.cancel_right ((hy.comp hf).ofFunctorIso h.symm)

/-- HTT 5.5.4.1 の、指定された辺集合に対する局所対象。 -/
def IsLocalObject (W : Set (X _⦋1⦌)) (z : X _⦋0⦌) : Prop :=
  ∀ e ∈ W, IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk (edgeOfSimplex e)) z

/-- 辺集合に対する局所対象の条件は同型で不変。 -/
lemma isLocalObject_iff_of_vertexIso (W : Set (X _⦋1⦌)) {z z' : X _⦋0⦌}
    (e : VertexIso z z') : IsLocalObject W z ↔ IsLocalObject W z' := by
  constructor <;> intro h f hf
  · exact (isLocalForHom_iff_of_vertexIso _ e).mp (h f hf)
  · exact (isLocalForHom_iff_of_vertexIso _ e).mpr (h f hf)

/-- 指定辺集合に対する局所対象の全部分複体。 -/
def localObjectsSubcomplex (W : Set (X _⦋1⦌)) : X.Subcomplex :=
  fullSubcomplexOnVertices X (IsLocalObject W)

/-- 局所対象の全部分複体は quasicategory。反射性は仮定しない。 -/
instance localObjectsSubcomplex_quasicategory (W : Set (X _⦋1⦌)) :
    Quasicategory (localObjectsSubcomplex W : SSet.{u}) :=
  inferInstanceAs (Quasicategory (fullSubcomplexOnVertices X (IsLocalObject W) : SSet.{u}))
/-- 局所性は任意単体集合パラメータの定値関手間 Hom の前合成を全単射にする。 -/
lemma isLocalForHom_constantHom_bijective {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    {z : X _⦋0⦌} (h : IsLocalForHom f z) (A : SSet.{u}) :
    Function.Bijective (fun α : ConstantFunctorHom A X y z ↦
      constantFunctorHomMap A f ≫ α) := by
  apply intervalFamilyComparison_bijective (intervalPrecompose z f)
    ((isLocalForHom_iff_interval f z).mp h).isSimplicialHomotopyEquivalence
  intro a
  exact (intervalPrecompose_family f a).symm

/-- 始域と終域が共に局所なら元の射は同型。パラメータ付き Hom から両逆を回収。 -/
lemma isIso_of_isLocalForHom_source_target {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (hx : IsLocalForHom f x) (hy : IsLocalForHom f y) : IsIso f := by
  let A := (Δ[0] : SSet.{u})
  let a : A _⦋0⦌ := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  let cf := constantFunctorHomMap A f
  obtain ⟨g, hg⟩ := (isLocalForHom_constantHom_bijective f hx A).2 (𝟙 _)
  have hg' : cf ≫ g = 𝟙 _ := hg
  have hgf : g ≫ cf = 𝟙 _ := by
    apply (isLocalForHom_constantHom_bijective f hy A).1
    change cf ≫ (g ≫ cf) = cf ≫ 𝟙 _
    rw [← Category.assoc, hg', Category.id_comp, Category.comp_id]
  have : IsIso cf := ⟨⟨g, hg', hgf⟩⟩
  let C := (hoFunctor.map (constantFunctorMap A X)).toFunctor
  let E := (hoFunctor.map (evaluateFunctorAt (Y := X) a)).toFunctor
  have hCE : C ⋙ E = 𝟭 (hoFunctor.obj X) := by
    change (hoFunctor.map (constantFunctorMap A X) ≫
      hoFunctor.map (evaluateFunctorAt (Y := X) a)).toFunctor = _
    rw [← Functor.map_comp, constantFunctorMap_evaluate, CategoryTheory.Functor.map_id]
    rfl
  have hm : C.map f =
      eqToHom (congrArg HomotopyCategory.mk (constantFunctorMap_vertex A x)) ≫ cf ≫
        eqToHom (congrArg HomotopyCategory.mk (constantFunctorMap_vertex A y)).symm := by
    simp [cf, constantFunctorHomMap, C, Category.assoc]
  have : IsIso (C.map f) := by rw [hm]; infer_instance
  have hi : IsIso ((C ⋙ E).map f) := inferInstanceAs (IsIso (E.map (C.map f)))
  rwa [hCE] at hi

end
end SerrePositivity.InfinityCategories.HomotopyLimits
