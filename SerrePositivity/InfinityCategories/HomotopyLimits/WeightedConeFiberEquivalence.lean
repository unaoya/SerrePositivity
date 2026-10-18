module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseVertexFiber

/-!
概要：weighted nerve から coherent cone の全空間への実際の射は各 fiber で同値。
方針：ULift と引き戻しの fiber を標準同型で同定し、一定の底の射に因子分解する。
規約：実際の全体の射が誘導する fiber 射を固定し、別の点ごとの同値に置き換えない。
使われ方：HTT 4.2.4.1、Kerodon §7.5.4 の切断空間の比較への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：反転した豊穣 Hom の持ち上げは weighted nerve の持ち上げた射影の fiber と同型。
方針：weighted nerve の標準 fiber 同型を持ち上げ、ULift と fiber の交換を合成する。
規約：底の頂点も ULift.up で表示する。
使われ方：HTT 4.2.4.1 の実際の fiber 射の始域の同定。 -/
noncomputable def weightedConeSourceFiberIso (F : I ⥤ C) (x : C) (i : I) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op ≅
    vertexFiber ((SSet.uliftFunctor.{v, u}).map
      (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
      (ULift.up (nerveVertex i)) :=
  (SSet.uliftFunctor.{v, u}).mapIso
    (weightedNerveFiberIso (simplicialHomDiagram F x ⋙ SSet.opFunctor) i) ≪≫
  uliftVertexFiberIso _ _

/-- 概要：始域の fiber 同型の包含は一定の底への包含の持ち上げと同じ。
方針：ULift と fiber の同型の包含の式を使い、weighted nerve の標準包含を計算する。
規約：同型の順方向についての厳密な式。
使われ方：HTT 4.2.4.1 の実際の fiber 射の因子分解。 -/
lemma weightedConeSourceFiberIso_hom_ι (F : I ⥤ C) (x : C) (i : I) :
    (weightedConeSourceFiberIso F x i).hom ≫
      vertexFiberι ((SSet.uliftFunctor.{v, u}).map
        (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
        (ULift.up (nerveVertex i)) =
    (SSet.uliftFunctor.{v, u}).map
      (weightedNerveConstantLift (simplicialHomDiagram F x ⋙ SSet.opFunctor) i) := by
  dsimp only [weightedConeSourceFiberIso, Iso.trans_hom]
  rw [Category.assoc, uliftVertexFiberIso_hom_ι]
  change (SSet.uliftFunctor.{v, u}).map
      (weightedNerveFiberMap (simplicialHomDiagram F x ⋙ SSet.opFunctor) i) ≫
      (SSet.uliftFunctor.{v, u}).map (vertexFiberι
        (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)) (nerveVertex i)) = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

/-- 概要：coherent cone の引き戻しの fiber は指定した終点の左 coslice fiber と同型。
方針：引き戻しの fiber の標準同型の後で strict な図式の頂点の式を移送する。
規約：終点は F(i) の標準頂点へ厳密に同定する。
使われ方：HTT 4.2.4.1 の実際の fiber 射の終域の同定。 -/
noncomputable def weightedConeTargetFiberIso (F : I ⥤ C) (x : C) (i : I) :
    vertexFiber (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
      (ULift.up (nerveVertex i)) ≅
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
      (coherentNerveVertex (F.obj i)) :=
  coherentConeProjectionFiberIso (strictCoherentDiagram F) (coherentNerveVertex x)
    (ULift.up (nerveVertex i)) ≪≫
  eqToIso (congrArg
    (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x))))
    (strictCoherentDiagram_vertex F i))

/-- 概要：終域の fiber 同型の包含は引き戻しの第一射影で誘導される。
方針：固定頂点の等号による移送を消し、引き戻しの fiber 同型の包含の式を使う。
規約：終点の正規化は元の全空間の射を変えない。
使われ方：HTT 4.2.4.1 の全体の比較射の fiber の計算。 -/
lemma weightedConeTargetFiberIso_hom_ι (F : I ⥤ C) (x : C) (i : I) :
    (weightedConeTargetFiberIso F x i).hom ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex (F.obj i)) =
    vertexFiberι (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
      (ULift.up (nerveVertex i)) ≫
      pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (strictCoherentDiagram F) := by
  dsimp only [weightedConeTargetFiberIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, vertexFiber_endpointTransport_ι
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (strictCoherentDiagram_vertex F i)]
  exact vertexFiberPullbackIso_hom_ι _ _ _

/-- 概要：構成済みの全体の比較射が誘導する実際の fiber 射。
方針：全体の底上の可換性から vertexFiberMap を作る。
規約：元の weightedCoherentConeComparison を固定する。
使われ方：HTT 4.2.4.1 の切断空間へ移す具体的な fiber 同値。 -/
noncomputable def weightedCoherentConeFiberMap (F : I ⥤ C) (x : C)
    (b : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌) :
    vertexFiber ((SSet.uliftFunctor.{v, u}).map
      (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor))) b ⟶
    vertexFiber (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x)) b :=
  vertexFiberMap _ _ (weightedCoherentConeComparison F x)
    (weightedCoherentConeComparison_over F x) b

/-- 概要：実際の fiber 射を両端の標準同型で移すと一定の底の構成済みの射になる。
方針：終域へ含めて比較し、引き戻しと fiber の持ち上げの包含の式を計算する。
規約：可換性の証明の選択に依存せず、射の厳密な等式で述べる。
使われ方：HTT 4.2.4.1 の実際の全体の比較射の fiber の同値性。 -/
lemma weightedCoherentConeFiberMap_factorization (F : I ⥤ C) (x : C) (i : I) :
    (weightedConeSourceFiberIso F x i).hom ≫
      weightedCoherentConeFiberMap F x (ULift.up (nerveVertex i)) ≫
      (weightedConeTargetFiberIso F x i).hom = weightedConstantCosliceFiberMap F x i := by
  apply vertexFiber_hom_ext
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (coherentNerveVertex (F.obj i))
  dsimp only [weightedCoherentConeFiberMap]
  simp only [Category.assoc]
  rw [weightedConeTargetFiberIso_hom_ι]
  rw [← Category.assoc (vertexFiberMap _ _ _ _ _) _ _, vertexFiberMap_ι]
  simp only [← Category.assoc]
  rw [weightedConeSourceFiberIso_hom_ι]
  change _ = weightedConstantCosliceMap F x i
  dsimp only [weightedCoherentConeComparison, weightedConstantCosliceMap]
  rw [Category.assoc, pullback.lift_fst]


/-- 概要：局所 Kan 性の下で全体の比較射が対象 i 上に誘導する fiber 射は同値。
方針：両端の標準同型で移した射の同値性から同型を消去する。
規約：一定の底の別の同値ではなく、全体の具体的な比較射が誘導する射を扱う。
使われ方：HTT 4.2.4.1 の係数図式全体の比較への入力。 -/
lemma weightedCoherentConeFiberMap_homotopyEquivalence_at
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    (F : I ⥤ C) (x : C) (i : I) :
    IsSimplicialHomotopyEquivalence
      (weightedCoherentConeFiberMap F x (ULift.up (nerveVertex i))) := by
  have := kanComplex_of_iso (pinchedLeftCosliceFiberIso
    (coherentNerveVertex x) (coherentNerveVertex (F.obj i)))
  have := kanComplex_of_iso (weightedConeSourceFiberIso F x i)
  have := kanComplex_of_iso (weightedConeTargetFiberIso F x i).symm
  have h₁ := (qCatEquivalenceOfIso (weightedConeSourceFiberIso F x i)).isQCatEquivalence
  have h₂ := (qCatEquivalenceOfIso (weightedConeTargetFiberIso F x i)).isQCatEquivalence
  have h : IsQCatEquivalence
      (((weightedConeSourceFiberIso F x i).hom ≫
        weightedCoherentConeFiberMap F x (ULift.up (nerveVertex i))) ≫
        (weightedConeTargetFiberIso F x i).hom) := by
    rw [Category.assoc, weightedCoherentConeFiberMap_factorization]
    exact (weightedConstantCosliceFiberMap_homotopyEquivalence F x i).isQCatEquivalence
  exact (h₁.cancel_left (h₂.cancel_right h)).isSimplicialHomotopyEquivalence

/-- 概要：局所 Kan 性の下で全体の比較射は全ての底の頂点上の fiber で同値。
方針：通常の nerve の零単体を元の圏の対象で表示し、対象上の結果を使う。
規約：底の頂点を標準頂点に制限する追加仮定はない。
使われ方：HTT 4.2.4.1 の left fibration と切断空間の比較。 -/
lemma weightedCoherentConeFiberMap_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    (F : I ⥤ C) (x : C) (b : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (weightedCoherentConeFiberMap F x b) := by
  rcases b with ⟨b⟩
  obtain ⟨i, rfl⟩ : ∃ i : I, b = nerveVertex i := ⟨b.obj 0, ComposableArrows.ext₀ rfl⟩
  exact weightedCoherentConeFiberMap_homotopyEquivalence_at F x i

end SerrePositivity.InfinityCategories.HomotopyLimits
