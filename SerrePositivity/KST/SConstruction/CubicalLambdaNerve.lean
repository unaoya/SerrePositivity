module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeNaturality

/-! # 元の Λ 標準単体からの全実 dg 関手の単体集合
概要：各標準単体の元の Λ からの実 dg 関手を、元の Λ 入力前合成で単体集合にする。
方針：元の入力関手の恒等・合成と実 dg 関手の厳密合成を使う。
規約：元の全対象・全 Hom・全退化を保持。使われ方：native dg nerve の実比較同型。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

private lemma id_comp {C : Type u} [DGCategory A C] (F : DGFunctor A C D) :
    DGFunctor.comp (DGFunctor.id C) F = F := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (Category.id_comp _)

private lemma comp_assoc {C B E : Type u} [DGCategory A C] [DGCategory A B] [DGCategory A E]
    (F : DGFunctor A C B) (G : DGFunctor A B E) (H : DGFunctor A E D) :
    DGFunctor.comp (DGFunctor.comp F G) H = DGFunctor.comp F (DGFunctor.comp G H) := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (Category.assoc _ _ _)

/-- 元の Λ 標準単体からの全実 dg 関手を、元の全入力前合成で作る単体集合。 -/
def cubicalLambdaNerve : SSet.{max u v} where
  obj n := DGFunctor A (CubicalLambda A (SSet.stdSimplex.obj n.unop)) D
  map f := ↾fun F => DGFunctor.comp (cubicalLambdaMap A (SSet.stdSimplex.map f.unop)) F
  map_id n := by
    ext F
    have h := (congrArg (cubicalLambdaMap A) ((SSet.stdSimplex.{u}).map_id n.unop)).trans
      (cubicalLambdaMap_id A (SSet.stdSimplex.obj n.unop))
    exact (congrArg (fun G => DGFunctor.comp G F) h).trans (id_comp A D F)
  map_comp f g := by
    ext F
    have h := (congrArg (cubicalLambdaMap A) ((SSet.stdSimplex.{u}).map_comp g.unop f.unop)).trans
      (cubicalLambdaMap_comp A (SSet.stdSimplex.map g.unop) (SSet.stdSimplex.map f.unop))
    exact (congrArg (fun G => DGFunctor.comp G F) h).trans (comp_assoc A D _ _ F)

/-- 元の全実 dg 関手の単体集合の標準次数は、元の同じ Λ からの実 dg 関手全体。 -/
lemma cubicalLambdaNerve_obj (N : ℕ) :
    (cubicalLambdaNerve A D) _⦋N⦌ = DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D := rfl

/-- 元の全作用素の単体作用は、元の標準単体写像の Λ による実前合成そのもの。 -/
lemma cubicalLambdaNerve_map_apply {M N : ℕ} (θ : ⦋M⦌ ⟶ ⦋N⦌)
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D) :
    (cubicalLambdaNerve A D).map θ.op F =
      DGFunctor.comp (cubicalLambdaMap A (SSet.stdSimplex.map θ)) F := rfl

end SerrePositivity.KST.SConstruction
