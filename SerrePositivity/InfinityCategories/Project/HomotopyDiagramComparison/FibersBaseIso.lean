module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SectionsBaseIso

/-!
概要：底の同型による left fibration と fiber・切断の同値性の移送。
方針：fiber には同じ全空間への包含を使い、同型との自然性から同値を消去する。
規約：元の全体の射を固定し、底への射影だけを同型で後合成する。
使われ方：HTT 4.2.4.1 の持ち上げた nerve から標準の添字圏への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

variable {K L E E' : SSet.{u}}

/-- 概要：left fibration の射影を底の同型で後合成しても left fibration。
方針：ホーンの右持ち上げ性が同型との合成で保たれることを使う。
規約：新しい全空間は元と同じ。
使われ方：HTT 4.2.4.1 の底の同型に沿う切断比較。 -/
instance leftFibration_postIso (p : E ⟶ K) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (e : K ≅ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (p ≫ e.hom) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem p e.hom _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：底を同型で移した射影の像の頂点上の fiber は元の fiber と同型。
方針：どちらの方向も全空間への包含で誘導し、固定条件を同型で移す。
規約：固定頂点 b は e.hom の零次成分で写す。
使われ方：HTT 4.2.4.1 の実際の fiber 射の同値性を底の変更で保つ。 -/
def vertexFiberBaseIso (p : E ⟶ K) (e : K ≅ L) (b : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ≫ e.hom) (e.hom.app (Opposite.op ⦋0⦌) b) := by
  let b' := e.hom.app (Opposite.op ⦋0⦌) b
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ (p ≫ e.hom) = SSet.const b' := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p ≫ e.hom) b' ≫ p = SSet.const b := by
    apply (cancel_mono e.hom).1
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
  refine {
    hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) hh
    inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p ≫ e.hom) b') hv
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (p ≫ e.hom) b'
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]

/-- 概要：底を移す fiber 同型は全空間への包含と厳密に可換。
方針：fiber の持ち上げの包含の式を計算する。
規約：同型の順方向。
使われ方：HTT 4.2.4.1 の fiber 比較の自然性。 -/
lemma vertexFiberBaseIso_hom_ι (p : E ⟶ K) (e : K ≅ L) (b : K _⦋0⦌) :
    (vertexFiberBaseIso p e b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p ≫ e.hom) (e.hom.app (Opposite.op ⦋0⦌) b) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := rfl

/-- 概要：底の同型による fiber の移送は全体の底上の射に自然。
方針：新しい fiber を全空間へ含めて両側を比較する。
規約：全体の同じ射 f から誘導される二つの fiber 射を比べる。
使われ方：HTT 4.2.4.1 の実際の fiber 同値の底の変更。 -/
lemma vertexFiberBaseIso_naturality (p : E ⟶ K) (q : E' ⟶ K) (e : K ≅ L)
    (f : E ⟶ E') (hf : f ≫ q = p) (b : K _⦋0⦌) :
    (vertexFiberBaseIso p e b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (p ≫ e.hom) (q ≫ e.hom) f (by rw [← Category.assoc, hf])
        (e.hom.app (Opposite.op ⦋0⦌) b) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b ≫ (vertexFiberBaseIso q e b).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (q ≫ e.hom) (e.hom.app (Opposite.op ⦋0⦌) b)
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, vertexFiberBaseIso_hom_ι,
    ← Category.assoc, vertexFiberBaseIso_hom_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]

/-- 概要：left fibration 間の指定した fiber 射の同値性は底の同型で保たれる。
方針：fiber の同型の自然性と同値の二対三を使う。
規約：底の頂点は同型の像で指定する。
使われ方：HTT 4.2.4.1 の全ての fiber の条件を標準の底へ移す。 -/
lemma vertexFiberMap_homotopyEquivalence_postIso
    (p : E ⟶ K) (q : E' ⟶ K) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (e : K ≅ L)
    (f : E ⟶ E') (hf : f ≫ q = p) (b : K _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (p ≫ e.hom) (q ≫ e.hom) f (by rw [← Category.assoc, hf])
        (e.hom.app (Opposite.op ⦋0⦌) b)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p b
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration q b
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration (p ≫ e.hom) (e.hom.app (Opposite.op ⦋0⦌) b)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration (q ≫ e.hom) (e.hom.app (Opposite.op ⦋0⦌) b)
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (vertexFiberBaseIso p e b)).isQCatEquivalence
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (vertexFiberBaseIso q e b)).isQCatEquivalence
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      ((vertexFiberBaseIso p e b).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (p ≫ e.hom) (q ≫ e.hom) f (by rw [← Category.assoc, hf])
          (e.hom.app (Opposite.op ⦋0⦌) b)) := by
    rw [vertexFiberBaseIso_naturality p q e f hf b]
    exact h.isQCatEquivalence.comp ht
  exact (hs.cancel_left hc).isSimplicialHomotopyEquivalence

/-- 概要：left fibration 間の切断比較の同値性は底の同型による変更の前後で同値。
方針：切断空間の同型の自然性の可換図式で同値を二対三により消去する。
規約：両側とも元の全体の射 f が誘導する切断写像。
使われ方：HTT 4.2.4.1 の既存の三形状の切断比較を持ち上げた底へ戻す。 -/
lemma simplicialSectionsMap_homotopyEquivalence_iff_postIso
    (p : E ⟶ K) (q : E' ⟶ K) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (e : K ≅ L)
    (f : E ⟶ E') (hf : f ≫ q = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f (by rw [← Category.assoc, hf]) :
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (p ≫ e.hom) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (q ≫ e.hom)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex q
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex (p ≫ e.hom)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex (q ≫ e.hom)
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialSectionsBaseIso p e)).isQCatEquivalence
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialSectionsBaseIso q e)).isQCatEquivalence
  constructor
  · intro h
    have hc := h.isQCatEquivalence.comp ht
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialSectionsBaseMap q e) at hc
    rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialSectionsBaseMap_naturality] at hc
    exact (hs.cancel_left hc).isSimplicialHomotopyEquivalence
  · intro h
    have hc := hs.comp h.isQCatEquivalence
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialSectionsBaseMap p e ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f (by rw [← Category.assoc, hf]) :
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (p ≫ e.hom) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (q ≫ e.hom))) at hc
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialSectionsBaseMap_naturality] at hc
    exact (ht.cancel_right hc).isSimplicialHomotopyEquivalence


/-- 概要：全ての fiber 射の同値性は底の同型による変更後の全ての頂点で成り立つ。
方針：新しい頂点を逆同型で戻し、同型の往復則で元の頂点へ同定する。
規約：底の新しい頂点に像であるという追加仮定を課さない。
使われ方：HTT 4.2.4.1 の三形状の切断比較への移送。 -/
lemma vertexFiberMap_isQCatEquivalence_postIso_all
    (p : E ⟶ K) (q : E' ⟶ K) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (e : K ≅ L)
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b))
    (c : L _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (p ≫ e.hom) (q ≫ e.hom) f (by rw [← Category.assoc, hf]) c) := by
  have hc : e.hom.app (Opposite.op ⦋0⦌) (e.inv.app (Opposite.op ⦋0⦌) c) = c :=
    ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id (Opposite.op ⦋0⦌)) c
  rw [← hc]
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration (p ≫ e.hom)
    (e.hom.app (Opposite.op ⦋0⦌) (e.inv.app (Opposite.op ⦋0⦌) c))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration (q ≫ e.hom)
    (e.hom.app (Opposite.op ⦋0⦌) (e.inv.app (Opposite.op ⦋0⦌) c))
  exact (vertexFiberMap_homotopyEquivalence_postIso p q e f hf
    (e.inv.app (Opposite.op ⦋0⦌) c) (h _)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
