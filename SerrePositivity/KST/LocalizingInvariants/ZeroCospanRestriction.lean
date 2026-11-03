module

public import SerrePositivity.InfinityCategories.Stable.CospanFamilies
public import SerrePositivity.InfinityCategories.Core.MappingSpaceTrivialFibration
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows

/-!
概要：第二枝の始点が零対象である cospan は、第一枝への制限と同値。
方針：零始点の辺の終点評価の境界充填を、cospan の二枝の貼り合わせへ移す。
規約：全パラメーターの族を保持する。使われ方：fiber 比較の cospan 制限の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ZeroCospan

variable (X : SSet.{u})

def zeroSecond (v : ((ihom (horn 2 2 : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  IsZeroSourceArrow (((pre horn₂₂.ι₁₂).app X).app (Opposite.op ⦋0⦌) v)

def diagrams : SSet.{u} :=
  (fullSubcomplexOnVertices _ (zeroSecond X) : SSet.{u})

def inclusion : diagrams X ⟶ (ihom (horn 2 2 : SSet.{u})).obj X :=
  (fullSubcomplexOnVertices _ (zeroSecond X)).ι

def first : diagrams X ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  inclusion X ≫ (pre horn₂₂.ι₀₂).app X

instance inclusion_mono : Mono (inclusion X) := by
  dsimp only [inclusion]
  infer_instance

def second : diagrams X ⟶ zeroSourceArrows X :=
  fullSubcomplexLift IsZeroSourceArrow
    (inclusion X ≫ (pre horn₂₂.ι₁₂).app X)
    (fun v ↦ fullSubcomplexOnVertices_vertex v)

lemma second_inclusion : second X ≫
    (fullSubcomplexOnVertices _ IsZeroSourceArrow).ι =
      inclusion X ≫ (pre horn₂₂.ι₁₂).app X := fullSubcomplexLift_ι _ _ _

lemma targets : first X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    second X ≫ zeroSourceArrowTarget X := by
  change first X ≫ evaluateFunctorAt (Y := X)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = (second X ≫
    (fullSubcomplexOnVertices _ IsZeroSourceArrow).ι) ≫
      evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  rw [second_inclusion]
  dsimp only [first]
  rw [Category.assoc, Category.assoc, stable_pre_evaluateFunctorAt,
    stable_pre_evaluateFunctorAt]
  rfl

instance first_trivialKanFibration [HasZeroVertex X] : TrivialKanFibration (first X) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let j : zeroSourceArrows X ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
    (fullSubcomplexOnVertices _ IsZeroSourceArrow).ι
  let t := evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have sqR : CommSq (a ≫ second X) (boundary n).ι (zeroSourceArrowTarget X) (b ≫ t) := by
    constructor
    rw [Category.assoc, ← targets, ← Category.assoc, sq.w, Category.assoc]
  have : HasLiftingProperty (boundary n).ι (zeroSourceArrowTarget X) :=
    TrivialKanFibration.mem (p := zeroSourceArrowTarget X) _ inferInstance
  let R := sqR.lift
  have hLR : b ≫ t = (R ≫ j) ≫ t := sqR.fac_right.symm
  let d := stable_cospanFamilyOfArrows b (R ≫ j) hLR
  have hd : (boundary n).ι ≫ d = a ≫ inclusion X := by
    apply stable_cospanFamily_hom_ext
    · rw [Category.assoc, stable_cospanFamilyOfArrows_left]
      exact sq.w.symm
    · rw [Category.assoc, stable_cospanFamilyOfArrows_right, ← Category.assoc,
        sqR.fac_left, Category.assoc]
      exact congrArg (fun k ↦ a ≫ k) (second_inclusion X)
  have hz (v : (Δ[n] : SSet.{u}) _⦋0⦌) : zeroSecond X (d.app _ v) := by
    have h := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) v)
      (stable_cospanFamilyOfArrows_right b (R ≫ j) hLR)
    change ((pre horn₂₂.ι₁₂).app X).app _ (d.app _ v) =
      (R.app _ v).val at h
    change IsZeroSourceArrow (((pre horn₂₂.ι₁₂).app X).app _ (d.app _ v))
    rw [h]
    exact fullSubcomplexOnVertices_vertex (R.app _ v)
  let F := fullSubcomplexLift (zeroSecond X) d hz
  have hFi : F ≫ inclusion X = d := fullSubcomplexLift_ι _ _ _
  refine CommSq.HasLift.mk' {
    l := F
    fac_left := ?_
    fac_right := ?_ }
  · apply (cancel_mono (inclusion X)).1
    rw [Category.assoc, hFi]
    exact hd
  · change F ≫ (inclusion X ≫ (pre horn₂₂.ι₀₂).app X) = b
    rw [← Category.assoc, hFi, stable_cospanFamilyOfArrows_left]

instance diagrams_quasicategory [Quasicategory X] : Quasicategory (diagrams X) :=
  fullSubcomplexOnVertices_quasicategory _ _

lemma first_isFullyFaithful [Quasicategory X] [HasZeroVertex X] :
    IsFullyFaithful (first X) := isFullyFaithful_of_trivialKanFibration _

end SerrePositivity.KST.LocalizingInvariants.ZeroCospan
