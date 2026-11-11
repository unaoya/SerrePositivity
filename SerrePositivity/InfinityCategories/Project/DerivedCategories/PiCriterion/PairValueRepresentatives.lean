module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.SphereClassPath
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredTotalDetection
public import SerrePositivity.KST.Spectra.FilteredLoopColimit
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：同じ基点の二つの正次数の類を、一つの値と同じ実際の基点 path で同時検出する。
方針：二球面の基点を pushout で貼り、その有限複体を一度だけ fiber へ移す。
規約：二代表を別々の path で検出して等式を比較しない。
使われ方：D の positive_equal_at_stage から全空間比較の正次数単射性を得る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra

private lemma groupMap_target_rebase {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (f : X ⟶ Y) {x : X _⦋0⦌} {y z : Y _⦋0⦌}
    (hf : f.app _ x = y) (hy : y = z) (hc : f.app _ x = z)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hc a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 Y) hy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hf a) := by
  simpa only [Category.comp_id, MonoidHom.comp_apply] using
    DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp f hf (𝟙 Y) hy hc) a

section FiniteDetection
variable {J : Type v} (X : J → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (T : SSet.{u}) [KanComplex T]
  (s : ∀ b : J, (X b).obj ⟶ T)
local notation "V" b => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.obj (X b)
local notation "j" b => s b

/-- 二つの類に共通の stage・基点・path と、その path 空間の二つの類を取れる。 -/
lemma finite_positive_pair_representative
    (hdetect : ∀ {K : SSet.{u}} [K.Finite] (f : K ⟶ T),
      ∃ b : J, ∃ g : K ⟶ (X b).obj, Nonempty (Homotopy f (g ≫ s b)))
    (n : ℕ) (x : T _⦋0⦌)
    (a : Fin 2 → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup T n x) :
    ∃ b : J, ∃ y : (V b) _⦋0⦌,
      ∃ β : Fin 2 → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (V b) n y,
      ∃ z : (KanPath.object T) _⦋0⦌,
      ∃ h₀ : (KanPath.evaluation T 0).app _ z = x,
      ∃ h₁ : (KanPath.evaluation T 1).app _ z = (j b).app _ y,
      ∃ γ : Fin 2 → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (KanPath.object T) n z,
        ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T 0) h₀ (γ k) = a k ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T 1) h₁ (γ k) =
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (j b) rfl (β k) := by
  let S := PointedSimplicialSet.sphere.{u} (n + 1)
  let A := PointedSimplicialSet.ofVertex T x
  let hx := PointedSimplicialSet.basepoint_ofVertex T x
  let ex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (Iso.refl T) (x := A.basepoint) (y := x) hx
  choose f hf using fun k : Fin 2 ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_surjective A n (ex.symm (a k))
  let K := pushout S.hom S.hom
  let Q : PointedSimplicialSet.{u} := Under.mk (S.hom ≫ pushout.inl S.hom S.hom)
  let r : K ⟶ T := pushout.desc (f 0).right (f 1).right
    ((Under.w (f 0)).trans (Under.w (f 1)).symm)
  let rp : Q ⟶ A := Under.homMk r (by
    change (S.hom ≫ pushout.inl S.hom S.hom) ≫ r = A.hom
    rw [Category.assoc, pushout.inl_desc]
    exact Under.w (f 0))
  let u₀ : S ⟶ Q := Under.homMk (pushout.inl S.hom S.hom) rfl
  let u₁ : S ⟶ Q := Under.homMk (pushout.inr S.hom S.hom)
    (pushout.condition (f := S.hom) (g := S.hom)).symm
  let u : Fin 2 → (S ⟶ Q) := ![u₀, u₁]
  have hur (k : Fin 2) : u k ≫ rp = f k := by
    fin_cases k
    · exact Under.UnderMorphism.ext (pushout.inl_desc _ _ _)
    · exact Under.UnderMorphism.ext (pushout.inr_desc _ _ _)
  have : (𝟙_ SSet.{u}).Finite := finite_of_iso PointedSimplicialSet.deltaZeroUnitIso.{u}
  have : K.Finite := by
    apply finite_of_isColimit (pushoutIsPushout S.hom S.hom)
    rintro (_ | _ | _) <;> dsimp [S] <;> infer_instance
  obtain ⟨b, g, ⟨H⟩⟩ := hdetect r
  let Y : PointedSimplicialSet.{u} := Under.mk (Q.hom ≫ g)
  let Z : PointedSimplicialSet.{u} := Under.mk (Y.hom ≫ j b)
  let P : PointedSimplicialSet.{u} := Under.mk (Q.hom ≫ KanPath.transpose H)
  have : KanComplex Y.right := inferInstanceAs (KanComplex (V b))
  have : KanComplex Z.right := inferInstanceAs (KanComplex T)
  have : KanComplex P.right := inferInstanceAs (KanComplex (KanPath.object T))
  let gp : Q ⟶ Y := Under.homMk g rfl
  let ip : Y ⟶ Z := Under.homMk (j b) rfl
  let hp : Q ⟶ P := Under.homMk (KanPath.transpose H) rfl
  let e₀ : P ⟶ A := Under.homMk (KanPath.evaluation T 0) (by
    change (Q.hom ≫ KanPath.transpose H) ≫ KanPath.evaluation T 0 = A.hom
    rw [Category.assoc, KanPath.transpose_zero]
    exact Under.w rp)
  let e₁ : P ⟶ Z := Under.homMk (KanPath.evaluation T 1) (by
    change (Q.hom ≫ KanPath.transpose H) ≫ KanPath.evaluation T 1 = Y.hom ≫ j b
    rw [Category.assoc, KanPath.transpose_one]
    rfl)
  have he₀ : hp ≫ e₀ = rp := Under.UnderMorphism.ext (KanPath.transpose_zero H)
  have he₁ : hp ≫ e₁ = gp ≫ ip := Under.UnderMorphism.ext (KanPath.transpose_one H)
  let h₀ := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint e₀
  let h₁ := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint e₁
  let hi := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint ip
  let γ (k : Fin 2) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n (u k ≫ hp)
  let β (k : Fin 2) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n (u k ≫ gp)
  have hs (k : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T 0) h₀ (γ k) =
      ex.symm (a k) := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_post n (u k ≫ hp) e₀
    rw [Category.assoc, he₀, hur] at h
    exact h.trans (hf k)
  have ht (k : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T 1) h₁ (γ k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (j b) hi (β k) := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_post n (u k ≫ hp) e₁
    rw [Category.assoc, he₁, ← Category.assoc] at h
    exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_post n (u k ≫ gp) ip).symm
  refine ⟨b, Y.basepoint, β, P.basepoint, h₀.trans hx, h₁.trans hi.symm, γ, ?_⟩
  intro k
  constructor
  · have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 T) hx (ex.symm (a k)) = a k := by
      change ex (ex.symm (a k)) = a k
      exact ex.apply_symm_apply _
    exact (groupMap_target_rebase n _ h₀ hx _ (γ k)).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 T) hx) (hs k)).trans ha)
  · exact (groupMap_target_rebase n _ h₁ hi.symm _ (γ k)).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 T) hi.symm) (ht k)).trans
        (groupMap_target_rebase n (j b) hi hi.symm rfl (β k)).symm)

end FiniteDetection

section Coherent
variable {B : SSet.{u}} [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F
local notation "V" b => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject
  (F.app (Opposite.op ⦋0⦌) (ULift.up b)))
local notation "j" b => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan F b

/-- 二つの類に共通の stage・基点・path と、その path 空間の二つの類を取れる。 -/
lemma total_positive_pair_representative (n : ℕ) (x : T _⦋0⦌)
    (a : Fin 2 → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup T n x) :
    ∃ b : B _⦋0⦌, ∃ y : (V b) _⦋0⦌,
      ∃ β : Fin 2 → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (V b) n y,
      ∃ z : (KanPath.object T) _⦋0⦌,
      ∃ h₀ : (KanPath.evaluation T 0).app _ z = x,
      ∃ h₁ : (KanPath.evaluation T 1).app _ z = (j b).app _ y,
      ∃ γ : Fin 2 → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (KanPath.object T) n z,
        ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T 0) h₀ (γ k) = a k ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T 1) h₁ (γ k) =
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (j b) rfl (β k) := by
  exact finite_positive_pair_representative
    (fun b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b)))
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan F)
    (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentFilteredTotalKan_finite_value_detection F f) n x a
end Coherent

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
