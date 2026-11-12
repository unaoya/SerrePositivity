module
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.Disk
/-!
概要：次数付き分裂射影を通る鎖自己写像から、全作用と可換する閉包含を作る。
方針：次数付き切断の後に自己写像を合成し、射影の次数ごとの分裂で鎖条件を検出する。
規約：因子化条件を明記し、ホモトピー同値だけから変形 retract を推論しない。
使われ方：正規化 bar の修正包含と二つの合成式を構成する代数的入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {B N : ModuleCategory R D} (p : B ⟶ N)
  (a : ∀ x : D, ∀ n : ℤ,
    ((moduleEvaluation R D x).obj N).X n ⟶ ((moduleEvaluation R D x).obj B).X n)
  (ha : ∀ (x y : D) (q i j : ℤ) (hij : i + q = j)
    (f : GradedHom R (Opposite.op x) (Opposite.op y) q),
    moduleActionComponent R D N x y q i j hij f ≫ a y j =
      a x i ≫ moduleActionComponent R D B x y q i j hij f)
  (hap : ∀ x n, a x n ≫ ((moduleEvaluation R D x).map p).f n = 𝟙 _)
  (e : B ⟶ B)
  (he : ∀ x n, ((moduleEvaluation R D x).map p).f n ≫ a x n ≫
      ((moduleEvaluation R D x).map e).f n = ((moduleEvaluation R D x).map e).f n)

include hap he in
lemma dgBarRetract_correctedSection_comm (x : D) (i j : ℤ) :
    (a x i ≫ ((moduleEvaluation R D x).map e).f i) ≫
        ((moduleEvaluation R D x).obj B).d i j =
      ((moduleEvaluation R D x).obj N).d i j ≫
        (a x j ≫ ((moduleEvaluation R D x).map e).f j) := by
  let P := (moduleEvaluation R D x).map p
  let E := (moduleEvaluation R D x).map e
  have h : P.f i ≫ ((a x i ≫ E.f i) ≫
      ((moduleEvaluation R D x).obj B).d i j) =
      P.f i ≫ (((moduleEvaluation R D x).obj N).d i j ≫ (a x j ≫ E.f j)) := by
    calc
      _ = (P.f i ≫ a x i ≫ E.f i) ≫
          ((moduleEvaluation R D x).obj B).d i j := by simp only [Category.assoc]
      _ = E.f i ≫ ((moduleEvaluation R D x).obj B).d i j := by rw [he x i]
      _ = ((moduleEvaluation R D x).obj B).d i j ≫ E.f j := E.comm i j
      _ = ((moduleEvaluation R D x).obj B).d i j ≫
          P.f j ≫ a x j ≫ E.f j := by rw [he x j]
      _ = _ := by rw [P.comm_assoc]
  have h' := congrArg (fun k => a x i ≫ k) h
  dsimp only [P] at h'
  simpa only [← Category.assoc, hap x i, Category.id_comp] using h'

def dgBarRetract_correctedSectionEvaluation (x : D) :
    (moduleEvaluation R D x).obj N ⟶ (moduleEvaluation R D x).obj B where
  f n := a x n ≫ ((moduleEvaluation R D x).map e).f n
  comm' i j _ := dgBarRetract_correctedSection_comm R D p a hap e he x i j

include ha in
lemma dgBarRetract_correctedSection_naturality :
    ∀ (x y : D) (q i j : ℤ) (hij : i + q = j)
      (f : GradedHom R (Opposite.op x) (Opposite.op y) q),
    moduleActionComponent R D N x y q i j hij f ≫
        (a y j ≫ ((moduleEvaluation R D y).map e).f j) =
      (a x i ≫ ((moduleEvaluation R D x).map e).f i) ≫
        moduleActionComponent R D B x y q i j hij f := by
  intro x y q i j hij f
  rw [← Category.assoc, ha, Category.assoc,
    moduleMorphism_actionComponent R D e, ← Category.assoc]


def dgBarRetract_correctedSection : N ⟶ B :=
  moduleMorphismMk R D
    (fun x => dgBarRetract_correctedSectionEvaluation R D p a hap e he x.unop)
    (closedFamily_of_action R _ (by
      intro x y q i j hij f z
      exact congrArg (fun k => k z)
        (dgBarRetract_correctedSection_naturality R D a ha e x.unop y.unop q i j hij f)))

lemma dgBarRetract_correctedSection_evaluation (x : D) (n : ℤ) :
    ((moduleEvaluation R D x).map
      (dgBarRetract_correctedSection R D p a ha hap e he)).f n =
      a x n ≫ ((moduleEvaluation R D x).map e).f n := by
  rw [dgBarRetract_correctedSection, moduleMorphismMk_eval]
  rfl

lemma dgBarRetract_projection_correctedSection :
    p ≫ dgBarRetract_correctedSection R D p a ha hap e he = e := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.Hom.ext
  funext n
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    dgBarRetract_correctedSection_evaluation]
  exact he x n

lemma dgBarRetract_correctedSection_projection (hep : e ≫ p = p) :
    dgBarRetract_correctedSection R D p a ha hap e he ≫ p = 𝟙 N := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.Hom.ext
  funext n
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    dgBarRetract_correctedSection_evaluation, Category.assoc, ← HomologicalComplex.comp_f,
    ← CategoryTheory.Functor.map_comp, hep, hap, CategoryTheory.Functor.map_id, HomologicalComplex.id_f]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
