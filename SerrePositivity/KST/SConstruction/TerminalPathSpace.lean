module
public import SerrePositivity.KST.Spectra.PathSpace

/-! # 終点を基点に固定した path 空間
概要：元の区間の終点を基点とする点つき区間と、その写像空間の始点評価を作る。
方針：端点包含を既存の始点基点の端点包含と余積の交換で比較する。
規約：区間を逆向きの単体的射で置換しない。使われ方：元の零行収縮の向きを保つ fiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

/-- 元の区間の頂点一を基点にした点つき区間。 -/
def terminalPointedInterval : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.ofVertex (Δ[1] : SSet.{u}) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- 非基点を元の区間の始点へ送る点つき端点包含。 -/
def terminalIntervalStart : 𝟙_ PointedSimplicialSet.{u} ⟶ terminalPointedInterval.{u} :=
  (PointedSimplicialSet.unitVertexEquiv terminalPointedInterval).symm
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 新しい端点包含の基礎射は既存の端点包含の二つの成分を交換する。 -/
lemma terminalIntervalStart_right : terminalIntervalStart.{u}.right =
    (coprod.braiding (𝟙_ SSet.{u}) (𝟙_ SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right := by
  change coprod.desc (SSet.const (X := 𝟙_ SSet.{u})
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
  apply coprod.hom_ext <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_right, coprod.braiding]

/-- 終点基点の区間の始点包含は元の単体集合で単射。 -/
instance terminalIntervalStart_mono : Mono terminalIntervalStart.{u}.right := by
  rw [terminalIntervalStart_right]
  infer_instance

/-- 非基点側の端点包含は元の区間の頂点零。 -/
lemma terminalIntervalStart_inl :
    (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫
      terminalIntervalStart.right =
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change coprod.inl ≫ coprod.desc _ _ = _
  exact coprod.inl_desc _ _

/-- 終点を標的の基点に固定する path の点つき空間。 -/
abbrev terminalPathSpace (B : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.basedHom terminalPointedInterval B

/-- Kan 標的の終点固定 path 空間は Kan。 -/
instance terminalPathSpace_kanComplex (B : PointedSimplicialSet.{u}) [KanComplex B.right] :
    KanComplex (terminalPathSpace B).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 終点固定 path の元の始点評価。 -/
def terminalPathStart (B : PointedSimplicialSet.{u}) : terminalPathSpace B ⟶ B :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed terminalIntervalStart B ≫
    (MonoidalClosed.unitIsoSelf (X := B)).hom

/-- 始点評価は元の端点包含の単射性によって Kan fibration。 -/
instance terminalPathStart_fibration (B : PointedSimplicialSet.{u}) [KanComplex B.right] :
    Fibration (terminalPathStart B).right := by
  let e := PointedSimplicialSet.forget.mapIso (MonoidalClosed.unitIsoSelf (X := B))
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre terminalIntervalStart B) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration terminalIntervalStart B
  change Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre terminalIntervalStart B ≫ e.hom)
  infer_instance

end SerrePositivity.KST.SConstruction
