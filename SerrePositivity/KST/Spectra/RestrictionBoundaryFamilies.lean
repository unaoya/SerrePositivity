module

public import SerrePositivity.KST.Spectra.RestrictionConnectingRepresentatives

/-!
概要：制限の連結射の代表を実際の単体パラメータ族として評価する。
方針：相対商の Hom の代表を uncurry し、源の商射とパラメータの最後の面を比較する。
規約：通常のテンソルは単体集合の直積。導来の同一視を使わない。
使われ方：Goerss–Jardine I §8、VIII §1。局所的な連結射の交代符号の計算。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B : SSet.{u}} (i : A ⟶ B) (Y : PointedSimplicialSet.{u})

/-- 概要：元の源から自由基点付き相対商への商射。
方針：追加基点以外の成分を標準 cofiber の射へ合成する。
規約：源 B に基点を指定しない。
使われ方：Goerss–Jardine VIII §1。相対商の写像の元の源での評価。 -/
def relativeProjection : B ⟶ (relativeSource i).right :=
  coprod.inl ≫ (pointedCofiberProjection (PointedObject.adjoinFunctor.map i)).right

@[reassoc]
lemma relativeProjection_restriction :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
        (pointedCofiberProjection (PointedObject.adjoinFunctor.map i)) Y).right ≫
        (freeHomIso B Y).hom.right =
      PointedObject.basedHomι (relativeSource i) Y ≫
        (MonoidalClosed.pre (relativeProjection i)).app Y.right := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _ Y ≫
    (PointedObject.basedHomι (PointedObject.adjoin B) Y ≫
      (MonoidalClosed.pre coprod.inl).app Y.right) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, Category.assoc,
    ← NatTrans.comp_app, ← MonoidalClosed.pre_map]
  rfl

lemma uncurry_constant_basepoint (B T : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    uncurry (SSet.const (X := T) (obj B Y).basepoint) =
      toUnit (B ⊗ T) ≫ Y.hom := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const (obj B Y) T, uncurry_natural_left]
  change B ◁ toUnit T ≫ uncurry (curry (snd B (𝟙_ SSet.{u}) ≫ Y.hom)) = _
  rw [uncurry_curry, ← Category.assoc, whiskerLeft_snd, comp_toUnit]

variable {n : ℕ}
  {s : (obj A Y).right.PtSimplex (n + 1) ((pre i Y).right.app _ (obj B Y).basepoint)}
  (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pre i Y).right (obj B Y).basepoint s)

/-- 概要：相対ホーン充填が表す元の源上のパラメータ族。
方針：通常の内部 Hom の充填射を uncurry する。
規約：パラメータの単体の次元は n+1。
使われ方：Goerss–Jardine I §8。連結射の最後の面を計算する族。 -/
def boundaryLiftFamily : B ⊗ (Δ[n + 1] : SSet.{u}) ⟶ Y.right := uncurry L.map

/-- 概要：相対商で表した連結射の代表を評価した族。
方針：pointed Hom の包含を通して代表単体を uncurry する。
規約：パラメータの単体の次元は n。
使われ方：Goerss–Jardine VIII §1。セル球面の向きの実際の評価。 -/
def boundaryLiftOutputFamily : (relativeSource i).right ⊗ (Δ[n] : SSet.{u}) ⟶ Y.right :=
  uncurry ((cofiberBoundarySimplex i Y L).map ≫ PointedObject.basedHomι (relativeSource i) Y)

/-- 概要：元の源の指定部分での充填族は底の代表のパラメータ族と一致する。
方針：相対充填の後合成式を uncurry の源の自然性へ移す。
規約：単体集合の射の厳密な等式。
使われ方：Goerss–Jardine I §8。セル境界の prescribed family の計算。 -/
@[reassoc]
lemma boundaryLiftFamily_source :
    i ▷ (Δ[n + 1] : SSet.{u}) ≫ boundaryLiftFamily i Y L = uncurry s.map := by
  have h := congrArg uncurry L.map_comp
  change uncurry (L.map ≫ (MonoidalClosed.pre i).app Y.right) = _ at h
  rw [uncurry_pre_app] at h
  exact h

/-- 概要：充填族は最後以外のパラメータ面で標的の基点に定数。
方針：充填の既知の面と通常の定数族の評価式を使う。
規約：面の添字は BoundaryLift と同じ。
使われ方：Goerss–Jardine I §8、VIII §1。局所的な連結射の矩形境界の条件。 -/
@[reassoc]
lemma boundaryLiftFamily_face (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    B ◁ (stdSimplex.δ j) ≫ boundaryLiftFamily i Y L =
      toUnit (B ⊗ (Δ[n] : SSet.{u})) ≫ Y.hom := by
  rw [boundaryLiftFamily, ← uncurry_natural_left, L.face_eq j hj,
    uncurry_constant_basepoint]

/-- 概要：相対商の代表の評価は元の充填族の最後のパラメータ面。
方針：代表の射影公式を通常の指数の源の前合成へ直して uncurry する。
規約：この式で最後の面の向きを固定し、符号の変更はまだ行わない。
使われ方：Goerss–Jardine VIII §1。連結射を球面的境界の交代式と比較する入力。 -/
@[reassoc]
lemma boundaryLiftOutputFamily_last :
    relativeProjection i ▷ (Δ[n] : SSet.{u}) ≫ boundaryLiftOutputFamily i Y L =
      B ◁ (stdSimplex.δ (Fin.last (n + 1))) ≫ boundaryLiftFamily i Y L := by
  have h := cofiberBoundarySimplex_projection i Y L
  rw [relativeProjection_restriction, ← Category.assoc] at h
  have hu := congrArg uncurry h
  erw [uncurry_pre_app Y.right ((cofiberBoundarySimplex i Y L).map ≫
    PointedObject.basedHomι (relativeSource i) Y) (relativeProjection i),
    uncurry_natural_left] at hu
  exact hu

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
