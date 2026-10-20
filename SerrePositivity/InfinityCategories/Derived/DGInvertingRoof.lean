module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverTerminal
public import SerrePositivity.InfinityCategories.Derived.RoofLocallyConstantPullback
public import SerrePositivity.InfinityCategories.Derived.RoofTerminalFiberCofinality
public import SerrePositivity.InfinityCategories.F1B.VertexFiberBaseChange
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.InfinityCategories.Derived.RoofFiberTransport

/-! # 任意の反転関手の実屋根

概要：任意の quasicategory への反転関手に対して、実分母上の屋根を作る。
方針：標的の representable 右ファイブレーションを実分母の始域写像で引き戻す。
規約：標的の dg 表示や安定性は要求しない。局所化普遍性そのものはまだ主張しない。
使われ方：任意標的に対する局所化の延長と、その写像空間の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 反転関手の値から任意の標的頂点へ入る、実分母上の屋根の全空間。 -/
def dgInvertingRoof (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) : SSet.{max u v} :=
  pullback (sliceOverProjection (SSet.yonedaEquiv.symm z))
    (dgVerdierOverSource A D P x ≫ F)

/-- 任意標的の屋根から実分母への射影。 -/
def dgInvertingRoofProjection (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :
    dgInvertingRoof A D P x F z ⟶ (dgVerdierOver A D P x : SSet) :=
  pullback.snd _ _

/-- 標的が quasicategory なら、任意標的の屋根射影は右ファイブレーション。 -/
instance dgInvertingRoofProjection_rightFibration (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :
    RightFibration (dgInvertingRoofProjection A D P x F z) :=
  rightFibration_pullback_snd _ _

/-- 任意標的の実屋根も quasicategory。 -/
instance dgInvertingRoof_quasicategory (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :
    Quasicategory (dgInvertingRoof A D P x F z) :=
  quasicategory_of_innerFibration (dgInvertingRoofProjection A D P x F z)

variable [IsDGPretriangulated A D]

/-- 実恒等分母の始域は元の頂点そのもの。 -/
lemma dgVerdierOverIdentityVertex_source (P : Set D) (x : D) :
    (dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌)
      (dgVerdierOverIdentityVertex A D P x) = Simplex.vertex x := by
  change SSet.yonedaEquiv (joinInl Δ[0] Δ[0] ≫
    SSet.const (Y := dgNerve A D) (Simplex.vertex x)) = _
  rw [SSet.comp_const]
  exact SSet.yonedaEquiv_const _

/-- 任意の反転関手の実屋根射影は、左ファイブレーションでもある。 -/
lemma dgInvertingRoofProjection_leftFibration (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) (z : Y _⦋0⦌) :
    LeftFibration (dgInvertingRoofProjection A D P x F z) := by
  apply roofRightFibration_pullback_leftFibration_of_inverts
  intro σ
  exact (isInvertibleEdge_congr (show
    ((edgeOfSimplex σ).map ((truncation 2).map (dgVerdierOverSource A D P x ≫ F))).edge =
      (edgeOfSimplex ((dgVerdierOverSource A D P x ≫ F).app
        (Opposite.op ⦋1⦌) σ)).edge from rfl)).mp
    (dgVerdierOverSource_inverts_of_inverts A D P x F hF (Set.mem_univ σ))

/-- 恒等分母上の fiber は、任意標的内の実 pinched Hom と厳密に同型。 -/
def dgInvertingRoofIdentityFiberIso (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :
    vertexFiber (dgInvertingRoofProjection A D P x F z)
      (dgVerdierOverIdentityVertex A D P x) ≅
        pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)) z :=
  cofinalVertexFiberBaseChangeIso _ _ (dgVerdierOverIdentityVertex A D P x) ≪≫
    eqToIso (congrArg (vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm z)))
      (congrArg (F.app (Opposite.op ⦋0⦌)) (dgVerdierOverIdentityVertex_source A D P x))) ≪≫
    (pinchedHomSliceFiberIso _ _).symm

/-- 固定された標的 Hom を、恒等分母の fiber として屋根全体へ含める。 -/
def dgInvertingFixedHomRoofMap (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :
    pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)) z ⟶
      dgInvertingRoof A D P x F z :=
  (dgInvertingRoofIdentityFiberIso A D P x F z).inv ≫
    vertexFiberι (dgInvertingRoofProjection A D P x F z)
      (dgVerdierOverIdentityVertex A D P x)

/-- 恒等 fiber の同型は、標的 slice への元の射影を回収する。 -/
lemma dgInvertingRoofIdentityFiberIso_hom_target (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :
    (dgInvertingRoofIdentityFiberIso A D P x F z).hom ≫
      (pinchedHomSliceFiberIso _ _).hom ≫
        vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm z))
          (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)) =
    vertexFiberι (dgInvertingRoofProjection A D P x F z)
      (dgVerdierOverIdentityVertex A D P x) ≫ pullback.fst _ _ := by
  dsimp only [dgInvertingRoofIdentityFiberIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [roofVertexFiberTransport_ι _
    (congrArg (F.app (Opposite.op ⦋0⦌)) (dgVerdierOverIdentityVertex_source A D P x))]
  exact cofinalVertexFiberBaseChangeIso_hom_ι _ _ _

/-- 固定 Hom の屋根への包含の実射側成分。 -/
lemma dgInvertingFixedHomRoofMap_target (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :
    dgInvertingFixedHomRoofMap A D P x F z ≫ pullback.fst _ _ =
      (pinchedHomSliceFiberIso _ _).hom ≫
        vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm z))
          (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)) := by
  dsimp only [dgInvertingFixedHomRoofMap]
  rw [Category.assoc, ← dgInvertingRoofIdentityFiberIso_hom_target,
    Iso.inv_hom_id_assoc]

/-- 固定 Hom の屋根への包含の実添字は恒等分母。 -/
lemma dgInvertingFixedHomRoofMap_projection (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :
    dgInvertingFixedHomRoofMap A D P x F z ≫ dgInvertingRoofProjection A D P x F z =
      SSet.const (dgVerdierOverIdentityVertex A D P x) := by
  dsimp only [dgInvertingFixedHomRoofMap]
  rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 任意の反転関手について、固定 Hom の屋根全体への包含は right cofinal。 -/
theorem dgInvertingFixedHomRoofMap_isRightCofinal (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) (z : Y _⦋0⦌) :
    IsRightCofinal (dgInvertingFixedHomRoofMap A D P x F z) := by
  have := dgInvertingRoofProjection_leftFibration A D P x F hF z
  exact (isRightCofinal_of_rightAnodyne _ (rightAnodyneExtensions.of_isIso
    (dgInvertingRoofIdentityFiberIso A D P x F z).inv)).comp
    (roofLeftFibration_terminalFiber_isRightCofinal
      (dgInvertingRoofProjection A D P x F z) (dgVerdierOverIdentityVertex A D P x)
      (dgVerdierOverIdentityVertex_isTerminal A D P x))

/-- 任意の反転関手の屋根全体は、標的の固定 Hom と弱ホモトピー同値。 -/
theorem dgInvertingFixedHomRoofMap_isWeakHomotopyEquivalence (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) (z : Y _⦋0⦌) :
    IsWeakHomotopyEquivalence (dgInvertingFixedHomRoofMap A D P x F z) :=
  (dgInvertingFixedHomRoofMap_isRightCofinal A D P x F hF z).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories
