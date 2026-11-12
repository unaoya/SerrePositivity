module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentReverseInvolution

/-!
概要：coherent nerve の反転と反対の単体的圏の coherent nerve の厳密な同型。
方針：coherent simplex を二回反転する往復則から逆射を作り、各次数で合成を計算する。
規約：既存の coherentNerveOppositeMap を順方向に使う。
使われ方：Kerodon §4.6.7（Tag 01LA） の左右の Hom の比較、HTT 4.2.4.1 の係数の向きの移送。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：coherent simplex を二回反転し二重反対を忘れると元の simplex。
方針：豊穣関手の反対の合成則と二重 unop の自然性で thickening の反転の往復則へ帰着する。
規約：対象と Hom の宇宙は異なってよい。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent nerve の二つの逆則。 -/
lemma coherentOppositeSimplex_involution {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {n : ℕ} (F : (SimplicialNerve C) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex F)).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop C) = F := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening.{u} n
  let Rop := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp R
  let Fopop := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F)
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop C
  let D := SimplicialThickening (ULift.{u} (Fin (n + 1)))
  change (R.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp (R.comp SSet
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F)))).comp SSet U = F
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp_comp]
  calc
    (R.comp SSet (Rop.comp SSet Fopop)).comp SSet U =
        ((R.comp SSet Rop).comp SSet Fopop).comp SSet U := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc R Rop Fopop]
    _ = (R.comp SSet Rop).comp SSet (Fopop.comp SSet U) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc _ _ _
    _ = (R.comp SSet Rop).comp SSet ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop D).comp SSet F) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop_naturality]
    _ = ((R.comp SSet Rop).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop D)).comp SSet F :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc _ _ _).symm
    _ = F := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening_involution]
      rfl

/-- 概要：二重 unop の豊穣関手の反対は反対圏の二重 unop と一致する。
方針：対象の op と unop の往復と恒等な Hom の射を比較する。
規約：対象の型の反対は構造として明示する。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent nerve の逆方向の合成則。 -/
lemma coherentEnrichedDoubleUnop_op (C : Type v) [EnrichedCategory SSet.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop Cᵒᵖ := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) (fun _ _ => ?_)
  exact Category.comp_id _

/-- 概要：反対の圏の coherent simplex を元の圏の反転した simplex へ戻す。
方針：もう一度頂点と path を反転し、二重反対から元へ移す。
規約：この段階では元の coherent nerve の同じ次数の元を返す。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent nerve の標準逆射。 -/
def coherentOppositeInverseSimplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (F : (SimplicialNerve Cᵒᵖ) _⦋n⦌) : (SimplicialNerve C) _⦋n⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex F).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop C)

/-- 概要：coherent simplex の反対の逆操作は反転した添字の制限と可換。
方針：反対の simplex の自然性を反転した添字で使い、二回の添字の反転を消去する。
規約：全ての面と退化を同時に扱う。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent nerve の逆射の単体的自然性。 -/
lemma coherentOppositeInverseSimplex_naturality {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (F : (SimplicialNerve Cᵒᵖ) _⦋n⦌) :
    coherentOppositeInverseSimplex ((SimplicialNerve Cᵒᵖ).map α.op F) =
      (SimplicialNerve C).map (SimplexCategory.rev.map α).op
        (coherentOppositeInverseSimplex F) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex_naturality (SimplexCategory.rev.map α) F
  rw [SimplexCategory.rev_map_rev_map] at h
  exact (congrArg (fun G : (SimplicialNerve Cᵒᵖᵒᵖ) _⦋m⦌ ↦
    G.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop C)) h).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc _ _ _)

/-- 概要：反対にした coherent simplex を戻すと元の simplex になる。
方針：二回の反転と二重 unop の往復則を使う。
規約：充填性なしの厳密な等式。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent nerve の単位則。 -/
lemma coherentOppositeInverseSimplex_opposite {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {n : ℕ} (F : (SimplicialNerve C) _⦋n⦌) :
    coherentOppositeInverseSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex F) = F :=
  coherentOppositeSimplex_involution F

/-- 概要：反対の逆操作の後で再び反対を取ると元の simplex になる。
方針：後合成への自然性と二重 unop の反対の式で、二回の反転の往復則へ帰着する。
規約：反対圏の simplex の厳密な等式。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent nerve の余単位則。 -/
lemma coherentOppositeSimplex_inverse {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {n : ℕ} (F : (SimplicialNerve Cᵒᵖ) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex (coherentOppositeInverseSimplex F) = F := by
  rw [coherentOppositeInverseSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex_post,
    coherentEnrichedDoubleUnop_op, coherentOppositeSimplex_involution]

/-- 概要：反対の単体的圏の coherent nerve から元の coherent nerve の反転への標準逆射。
方針：各 simplex の反対の逆操作とその自然性を使う。
規約：Kan 性や quasicategory 性は要求しない。
使われ方：Kerodon §4.6.7（Tag 01LA） の右 Hom と左 coslice の向きを移す同型の逆。 -/
def coherentNerveOppositeInverse (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    SimplicialNerve Cᵒᵖ ⟶ (SimplicialNerve C).op where
  app _ := ↾fun F ↦ SSet.opObjEquiv.symm (coherentOppositeInverseSimplex F)
  naturality d e α := by
    obtain ⟨⟨n⟩⟩ := d
    obtain ⟨⟨m⟩⟩ := e
    apply ConcreteCategory.hom_ext
    intro F
    apply SSet.opObjEquiv.injective
    exact coherentOppositeInverseSimplex_naturality α.unop F

/-- 概要：coherent nerve の反転は反対の単体的圏の coherent nerve と厳密に同型。
方針：既存の標準射と構成した逆射の合成を各 simplex の往復則で計算する。
規約：全ての単体的圏で成立し、Kan 性の仮定は不要。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の左右の係数の向きの自然な移送。 -/
def coherentNerveOppositeIso (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    (SimplicialNerve C).op ≅ SimplicialNerve Cᵒᵖ where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap C
  inv := coherentNerveOppositeInverse C
  hom_inv_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro F
    apply SSet.opObjEquiv.injective
    exact coherentOppositeInverseSimplex_opposite (SSet.opObjEquiv F)
  inv_hom_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro F
    exact coherentOppositeSimplex_inverse F

/-- 概要：反対の coherent nerve への既存の標準射は同型射である。
方針：構成した厳密な同型の順方向と定義的に同じ射であることを使う。
規約：Kan 性を要求しない。
使われ方：Kerodon §4.6.7（Tag 01LA） の左右の Hom での端点の等式の消去。 -/
instance coherentNerveOppositeMap_isIso (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap C) := by
  change IsIso (coherentNerveOppositeIso C).hom
  infer_instance

/-- 概要：反対の coherent nerve の標準逆射は反対の対象を元の対象の頂点へ戻す。
方針：零単体をその対象で検出し、二重 unop の対象を計算する。
規約：頂点の像は厳密な等式である。
使われ方：Kerodon §4.6.7（Tag 01LA） の右 pinched Hom から左 coslice への二端点の同定。 -/
lemma coherentNerveOppositeInverse_vertex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (x : C) :
    (coherentNerveOppositeInverse C).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op x)) = SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) := by
  apply SSet.opObjEquiv.injective
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv C).symm.injective
  rfl

/-- 概要：反対の coherent nerve の標準逆射も豊穣関手に自然。
方針：順方向の自然性の両側に構成した逆射を合成し、二つの往復則で消去する。
規約：C と D の対象の宇宙を v に揃える。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の左側の係数の自然な移送。 -/
lemma coherentNerveOppositeInverse_post {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet C D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F) ≫ coherentNerveOppositeInverse D =
      coherentNerveOppositeInverse C ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F) := by
  let eC := coherentNerveOppositeIso C
  let eD := coherentNerveOppositeIso D
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap_post F
  change SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F) ≫ eD.hom =
    eC.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F) at hn
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F) ≫ eD.inv =
    eC.inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F)
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F) ≫ eD.inv =
        (eC.inv ≫ (eC.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F))) ≫ eD.inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (eC.inv ≫ (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F) ≫ eD.hom)) ≫ eD.inv := by
      rw [← hn]
    _ = eC.inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNervePost F) := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
