module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomClassificationLaws
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.LeftFibrationHomClasses

/-!
概要：元の分類図式間の射を、底を保つ元の left fibration 間の実際の射へ戻す。
方針：充満忠実な分類の Hom の逆と、coherent nerve の辺から通常の射への回収を使う。
規約：元の leftClassificationHom 自身で指定射を回収する。
使われ方：P-12 の coslice の実 Hom 制限を、元の分類図式の Hom 普遍性へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：頂点の等式で正規化した全 Hom の作用。
方針：ホモトピー圏の関手の Hom 作用を元の両端点へ輸送する。
規約：任意の単体集合を許す。使われ方：具体的な分類写像の元の端点への輸送。 -/
def normalizedVertexHomMap {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌}
    (hx : x' = f.app (Opposite.op ⦋0⦌) x) (hy : y' = f.app (Opposite.op ⦋0⦌) y)
    (a : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    (HomotopyCategory.mk x' : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y' :=
  eqToHom (congrArg HomotopyCategory.mk hx) ≫
    (hoFunctor.map f).toFunctor.map a ≫ eqToHom (congrArg HomotopyCategory.mk hy).symm

/-- 概要：充満忠実な写像の正規化済みの Hom 作用は全単射。
方針：元の Hom 全単射と両端点の同型による Hom の同値を合成する。
規約：指定した端点等式を使う。使われ方：分類の実 Hom の持ち上げと反映。 -/
lemma normalizedVertexHomMap_bijective {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (f : X ⟶ Y) (hf : IsFullyFaithful f)
    {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌}
    (hx : x' = f.app (Opposite.op ⦋0⦌) x) (hy : y' = f.app (Opposite.op ⦋0⦌) y) :
    Function.Bijective (normalizedVertexHomMap f hx hy) := by
  let ep : VertexIso x' (f.app (Opposite.op ⦋0⦌) x) :=
    eqToIso (congrArg HomotopyCategory.mk hx)
  let eq : VertexIso y' (f.app (Opposite.op ⦋0⦌) y) :=
    eqToIso (congrArg HomotopyCategory.mk hy)
  let e := (Equiv.ofBijective _ (hf.homotopyCategoryMap_bijective x y)).trans
    (Iso.homCongr ep.symm eq.symm)
  have he : (e : _ → _) = normalizedVertexHomMap f hx hy := rfl
  rw [← he]
  exact e.bijective

/-- 概要：実全空間射の分類は元の分類写像の Hom 作用を両頂点で正規化したもの。
方針：分類の定義中の端点移送をホモトピー圏の共役として展開する。
規約：元の比較辺を保持する。使われ方：分類の充満忠実性の実射への適用。 -/
def leftClassificationNormalizedMap
    {E H B : SSet.{u}}
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (α : (HomotopyCategory.mk (leftFibrationInfinityVertex p) :
        hoFunctor.obj (LeftFibrationInfinity B)) ⟶
      HomotopyCategory.mk (leftFibrationInfinityVertex q)) :
    FunctorHom (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q) :=
  normalizedVertexHomMap (leftStraighteningInfinityMap B)
    (x := leftFibrationInfinityVertex p) (y := leftFibrationInfinityVertex q)
    (x' := functorVertex (leftStraighteningInfinityDiagram p))
    (y' := functorVertex (leftStraighteningInfinityDiagram q))
    (leftStraighteningInfinityDiagram_vertex p) (leftStraighteningInfinityDiagram_vertex q) α

/-- 概要：元の分類比較の正規化は元の coherent な辺の分類と一致する。
方針：端点移送の式を展開する。規約：元の射を使う。
使われ方：分類の充満忠実性による実全空間射の回収。 -/
lemma leftClassificationHom_eq_normalizedMap
    {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) :
    leftClassificationHom p q f hf =
      leftClassificationNormalizedMap p q
        (Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated) := by
  simp only [leftClassificationHom, homMk_edge_ofEq, leftClassificationNormalizedMap,
    normalizedVertexHomMap]
  rfl

/-- 概要：元の分類写像の正規化済みの全 Hom 作用は全単射。
方針：分類の充満忠実性を同じ指定頂点等式で移す。
規約：底は quasicategory。使われ方：元の実全空間射の分類の回収と反映。 -/
lemma leftClassificationNormalizedMap_bijective
    {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q] :
    Function.Bijective (leftClassificationNormalizedMap p q) :=
  normalizedVertexHomMap_bijective (leftStraighteningInfinityMap B)
    (leftStraighteningInfinityMap_isFullyFaithful B)
    (x := leftFibrationInfinityVertex p) (y := leftFibrationInfinityVertex q)
    (leftStraighteningInfinityDiagram_vertex p) (leftStraighteningInfinityDiagram_vertex q)

/-- 概要：元の分類図式の任意の射は、底を保つ元の全空間射の分類で表せる。
方針：分類の充満忠実性で Hom を戻し、その辺を coherent nerve の通常の射へ回収する。
規約：指定した射そのものを回収する。使われ方：実相対 Hom の全射性による Hom 普遍性。 -/
lemma exists_leftClassificationHom
    {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (α : FunctorHom (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q)) :
    ∃ (f : E ⟶ H) (hf : f ≫ q = p), leftClassificationHom p q f hf = α := by
  obtain ⟨a, ha⟩ := (leftClassificationNormalizedMap_bijective p q).surjective α
  obtain ⟨t, ht⟩ := homotopyCategory_homMk_surjective
    (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q) a
  let s := SSet.Edge.ofTruncated t
  let g : leftFibrationObjectOf p ⟶ leftFibrationObjectOf q := coherentNerveEdgeToHom s
  have hg : (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from
      Over.homMk g.left g.w) = g := Over.homMk_eta g _
  have he : leftFibrationInfinityEdge p q g.left g.w = s := by
    change coherentNerveEdge (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from
      Over.homMk g.left g.w) = s
    rw [hg]
    exact coherentNerveEdge_hom s
  refine ⟨g.left, g.w, ?_⟩
  rw [leftClassificationHom_eq_normalizedMap, he]
  change leftClassificationNormalizedMap p q (Truncated.HomotopyCategory.homMk t) = α
  rw [ht]
  exact ha

/-- 概要：実全空間射の分類が等しいことと元の相対 Hom 内で同型なことは同値。
方針：正規化した分類の単射性と、coherent な辺の類からの相対同型の回収を合成する。
規約：元の二つの底上の射を固定する。使われ方：実 Hom 制限の単射性を分類後へ移す。 -/
lemma leftClassificationHom_eq_iff_relativeVertexIso
    {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f g : E ⟶ H) (hf : f ≫ q = p) (hg : g ≫ q = p) :
    leftClassificationHom p q f hf = leftClassificationHom p q g hg ↔
      Nonempty (VertexIso (relativeFunctorVertex q p f hf) (relativeFunctorVertex q p g hg)) := by
  constructor
  · intro h
    rw [leftClassificationHom_eq_normalizedMap, leftClassificationHom_eq_normalizedMap] at h
    exact relativeVertexIso_of_leftFibrationEdge_homEq p q f g hf hg
      ((leftClassificationNormalizedMap_bijective p q).injective h)
  · rintro ⟨h⟩
    exact leftClassificationHom_eq_of_relativeVertexIso p q f g hf hg h

end SerrePositivity.InfinityCategories.F2.Presentable
