module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomFromLongChain
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedLeftProjection

/-!
概要：実際の twisted arrow の単体を長い射列から読み戻し、両端射影を保持する。
方針：既存の edgewise の標準単体同型と左右の包含の座標式を使う。
規約：読み戻しは各次数の指定写像であり、ここでは比較の逆関係をまだ主張しない。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の Hom 模型比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {n : ℕ}

/-- 長い射列からの読み戻しの標的射列は元の右半分である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、復元の右制限の法則。 -/
lemma ordinaryHomFromLongChain_target (L : ComposableArrows C (n + n + 1)) :
    ordinaryHomFromLongChain L ⋙ ordinaryHomElementsProjection C ⋙
      CategoryTheory.Prod.snd Cᵒᵖ C = (joinRightOrderHom n n).toFunctor ⋙ L := rfl

private lemma longLeftIndex_eq (i : Fin (n + 1)) :
    edgewiseLeftVertex n i = joinLeftOrderHom n n i.rev := by
  apply Fin.ext
  simp only [edgewiseLeftVertex, joinLeftOrderHom, OrderHom.coe_mk, Fin.val_rev]
  omega

private lemma longMapOp_heq (L : ComposableArrows C (n + n + 1))
    {i j i' j' : Fin (n + n + 1 + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : HEq (L.map f).op (L.map g).op := by
  subst i' j'
  have hh : f = g := Subsingleton.elim _ _
  subst g
  rfl

/-- 長い射列からの読み戻しの源射列は元の左半分の反転である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、復元の左制限の法則。 -/
lemma ordinaryHomFromLongChain_source (L : ComposableArrows C (n + n + 1)) :
    ordinaryHomFromLongChain L ⋙ ordinaryHomElementsProjection C ⋙
      CategoryTheory.Prod.fst Cᵒᵖ C =
      nerveReverseChain ((joinLeftOrderHom n n).toFunctor ⋙ L) := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i
    exact congrArg (fun k => Opposite.op (L.obj k)) (longLeftIndex_eq i)
  · intro i j h
    exact longMapOp_heq L (longLeftIndex_eq j) (longLeftIndex_eq i) _ _

/-- 実際の edgewise の長い単体の右半分は指定した右射影の全射列である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、標準単体同型の右制限の法則。 -/
lemma edgewiseLongChain_right (f : (TwistedArrow (nerve C)) _⦋n⦌) :
    (joinRightOrderHom n n).toFunctor ⋙ edgewiseSimplexEquiv (nerve C) n f =
      (edgewiseRight (nerve C)).app (Opposite.op ⦋n⦌) f := by
  change (nerve C).map (SimplexCategory.mkHom (joinRightOrderHom n n)).op
      (SSet.yonedaEquiv ((edgewiseWeightIso n).inv ≫ f)) =
    SSet.yonedaEquiv (joinInr _ _ ≫ f)
  rw [SSet.yonedaEquiv_naturality]
  have he : stdSimplex.map (SimplexCategory.mkHom (joinRightOrderHom n n)) ≫
      (edgewiseWeightIso.{u} n).inv = joinInr _ _ := by
    have hh := congrArg (fun q => q ≫ (edgewiseWeightIso.{u} n).inv)
      (edgewiseWeightIso_inr.{u} n)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm
  rw [← Category.assoc, he]

/-- 実際の edgewise の長い単体の左半分の反転は指定した左射影である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、反対 nerve の指定比較を含む左制限の法則。 -/
lemma edgewiseLongChain_left (f : (TwistedArrow (nerve C)) _⦋n⦌) :
    nerveReverseChain ((joinLeftOrderHom n n).toFunctor ⋙ edgewiseSimplexEquiv (nerve C) n f) =
      nerveOppositeMap.app (Opposite.op ⦋n⦌)
        ((edgewiseLeft (nerve C)).app (Opposite.op ⦋n⦌) f) := by
  change nerveReverseChain ((nerve C).map (SimplexCategory.mkHom (joinLeftOrderHom n n)).op
      (SSet.yonedaEquiv ((edgewiseWeightIso n).inv ≫ f))) =
    nerveReverseChain (SSet.yonedaEquiv ((stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫ f))
  rw [SSet.yonedaEquiv_naturality]
  have he : stdSimplex.map (SimplexCategory.mkHom (joinLeftOrderHom n n)) ≫
      (edgewiseWeightIso.{u} n).inv = (stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ := by
    have hh : (stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫
        (edgewiseWeightIso.{u} n).hom =
        stdSimplex.map (SimplexCategory.mkHom (joinLeftOrderHom n n)) := by
      rw [edgewiseWeightIso_inl, Iso.inv_hom_id_assoc]
    have hh' := congrArg (fun q => q ≫ (edgewiseWeightIso.{u} n).inv) hh
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh'.symm
  rw [← Category.assoc, he, Category.assoc]

/-- 実際の twisted arrow の単体から元の Hom の元の圏の射列を読み戻す。
Kerodon Proposition 8.1.1.10（Tag 03JN）、比較の逆向きの指定写像の各次数の部分。 -/
def ordinaryHomTwistedRead (f : (TwistedArrow (nerve C)) _⦋n⦌) :
    ComposableArrows (OrdinaryHomElements C) n :=
  ordinaryHomFromLongChain (edgewiseSimplexEquiv (nerve C) n f)

/-- 読み戻しは指定した右射影の全射列を保つ。
Kerodon Proposition 8.1.1.10（Tag 03JN）、逆向きの比較の右制限の法則。 -/
lemma ordinaryHomTwistedRead_target (f : (TwistedArrow (nerve C)) _⦋n⦌) :
    ordinaryHomTwistedRead f ⋙ ordinaryHomElementsProjection C ⋙
      CategoryTheory.Prod.snd Cᵒᵖ C = (edgewiseRight (nerve C)).app (Opposite.op ⦋n⦌) f := by
  rw [ordinaryHomTwistedRead, ordinaryHomFromLongChain_target, edgewiseLongChain_right]

/-- 読み戻しは指定した反対 nerve 比較を介して左射影の全射列を保つ。
Kerodon Proposition 8.1.1.10（Tag 03JN）、逆向きの比較の左制限の法則。 -/
lemma ordinaryHomTwistedRead_source (f : (TwistedArrow (nerve C)) _⦋n⦌) :
    ordinaryHomTwistedRead f ⋙ ordinaryHomElementsProjection C ⋙
      CategoryTheory.Prod.fst Cᵒᵖ C =
      nerveOppositeMap.app (Opposite.op ⦋n⦌)
        ((edgewiseLeft (nerve C)).app (Opposite.op ⦋n⦌) f) := by
  rw [ordinaryHomTwistedRead, ordinaryHomFromLongChain_source, edgewiseLongChain_left]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
