module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.F1.Transport.EdgeTransport
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransport
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberKan
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：left fibration の transport と底の引き戻しの整合性。
方針：引き戻し内の prism を第一射影で写し、標準 fiber 同型で両端を移す。
規約：底の quasicategory 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、普遍 left fibration の作用を図式の復元と比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：left fibration の引き戻しの第二射影は left fibration。
方針：left anodyne 射に関する右持ち上げ性の引き戻し安定性を使う。
規約：第一引数を引き戻す射、第二引数を底の変更とする。
使われ方：Kerodon Corollary 5.6.0.6、引き戻しの transport の構成。 -/
instance leftFibration_pullback_snd {E B C : SSet.{u}} (p : E ⟶ B) (k : C ⟶ B)
    [LeftFibration p] : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：fiber 同型の逆を全空間へ含めて第一射影で写すと元の fiber の包含になる。
方針：順方向の包含公式の左に同型の逆を合成する。
規約：式は元の全空間 E への射の等式。
使われ方：Kerodon Corollary 5.6.0.6、引き戻した transport の始点条件。 -/
lemma vertexFiberPullbackIso_inv_ι_fst {E B C : SSet.{u}}
    (p : E ⟶ B) (k : C ⟶ B) (a : C _⦋0⦌) :
    (vertexFiberPullbackIso p k a).inv ≫ vertexFiberι (pullback.snd p k) a ≫
      pullback.fst p k = vertexFiberι p (k.app (Opposite.op ⦋0⦌) a) := by
  rw [← vertexFiberPullbackIso_hom_ι, Iso.inv_hom_id_assoc]

/-- 概要：引き戻しの transport の証人は fiber 同型を介して元の射影の証人を与える。
方針：始点 fiber の同型の逆で prism を制限し、第一射影で写す。
規約：元の底の辺は k による e の像。
使われ方：Kerodon Corollary 5.6.0.6、普遍射影の輸送と unstraightening の輸送の比較。 -/
lemma IsEdgeTransport.pullback {E B C : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : C ⟶ B)
    {a b : C _⦋0⦌} (e : SSet.Edge a b)
    {T : vertexFiber (pullback.snd p k) a ⟶ vertexFiber (pullback.snd p k) b}
    (hT : IsEdgeTransport (pullback.snd p k) e T) :
    IsEdgeTransport p (e.map k)
      ((vertexFiberPullbackIso p k a).inv ≫ T ≫ (vertexFiberPullbackIso p k b).hom) := by
  obtain ⟨H, hH₀, hH₁, hHp, _⟩ := hT
  refine ⟨(Δ[1] ◁ (vertexFiberPullbackIso p k a).inv) ≫ H ≫ pullback.fst p k,
    ?_, ?_, ?_, fun _ ↦ isCocartesianEdge_of_leftFibration _ _⟩
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      ← Category.assoc (prismEndpoint 0 _),
      hH₀, vertexFiberPullbackIso_inv_ι_fst]
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      ← Category.assoc (prismEndpoint 1 _),
      hH₁]
    simp only [Category.assoc, vertexFiberPullbackIso_hom_ι]
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc H, hHp,
      ← Category.assoc, ← Category.assoc, whiskerLeft_fst, Category.assoc]
    congr 1
    exact SSet.yonedaEquiv_symm_comp _ k

/-- 概要：引き戻しの標準 transport は fiber 同型で移すと像の辺の標準 transport と関手同型。
方針：引き戻しの証人を移した後、left fibration の transport の一意性を適用する。
規約：同型は元の終点 fiber 内で取る。
使われ方：Kerodon Proposition 5.2.2.8、Corollary 5.6.0.6、底の変更と選択した輸送の整合性。 -/
noncomputable def edgeTransport_pullbackIso {E B C : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : C ⟶ B)
    {a b : C _⦋0⦌} (e : SSet.Edge a b) :
    FunctorIso
      ((vertexFiberPullbackIso p k a).inv ≫ edgeTransport (pullback.snd p k) e ≫
        (vertexFiberPullbackIso p k b).hom)
      (edgeTransport p (e.map k)) :=
  (IsEdgeTransport.functorIso p (e.map k)
    ((edgeTransport_isTransport (pullback.snd p k) e).pullback p k e)
    (edgeTransport_isTransport p (e.map k))).some

/-- 概要：引き戻した辺の transport の同値性は、元の底の像の辺の transport の同値性と一致する。
方針：transport の関手同型と、両端の fiber 同型に同値の二対三則を使う。
規約：同値性は Kan fiber 間の quasicategory 同値として述べる。
使われ方：Kerodon Corollary 5.6.0.6、普遍射影の作用の同値性を図式の復元から判定する。 -/
lemma edgeTransport_pullback_isQCatEquivalence_iff {E B C : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : C ⟶ B)
    {a b : C _⦋0⦌} (e : SSet.Edge a b) :
    IsQCatEquivalence (edgeTransport (pullback.snd p k) e) ↔
      IsQCatEquivalence (edgeTransport p (e.map k)) := by
  have ha := (qCatEquivalenceOfIso (vertexFiberPullbackIso p k a).symm).isQCatEquivalence
  have hb := (qCatEquivalenceOfIso (vertexFiberPullbackIso p k b)).isQCatEquivalence
  have h := edgeTransport_pullbackIso p k e
  constructor
  · intro he
    exact (ha.comp (he.comp hb)).ofFunctorIso h
  · intro he
    exact ha.cancel_left (hb.cancel_right (he.ofFunctorIso h.symm))

end SerrePositivity.InfinityCategories
