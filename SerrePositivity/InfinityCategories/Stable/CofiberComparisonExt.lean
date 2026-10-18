module
public import SerrePositivity.InfinityCategories.Stable.CofiberComparisonUniqueness

/-! # Cofiber 比較の始点成分による判定

概要：普遍四角形から suspension 四角形への h の射は始点成分だけで決まる。
方針：任意の射を関手辺で表し、余錐の射影と span の始点評価の忠実性を使う。
規約：始点の成分は恒等射である必要はない。
使われ方：S4 の接続射の合成と suspension の変更の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：関手辺をホモトピーに直してから辺に戻すと元の辺になる。
方針：curry と uncurry、Yoneda の両逆性を使う。
規約：quasicategory 性は不要。使われ方：任意の h の射の代表による照合。 -/
lemma stableFunctorEdge_homotopy_roundtrip {A X : SSet.{u}} {F G : A ⟶ X}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (functorVertex F) (functorVertex G)) :
    functorEdgeOfSimplicialHomotopy (simplicialHomotopyOfFunctorEdge e) = e := by
  apply SSet.Truncated.Edge.ext
  change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge))) = e.edge
  rw [curry_uncurry, Equiv.apply_symm_apply]

/-- 概要：余極限余錐間の任意の h の二射は図式への制限が一致すれば等しい。
方針：二射を辺で表してホモトピーに戻し、余錐の比較の一意性を適用する。
規約：X は quasicategory、両端は余極限。使われ方：比較の合成の判定。 -/
lemma colimitCocone_hom_ext {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (hc : IsColimitCone c) (hd : IsColimitCone d)
    {a b : (SSet.HomotopyCategory.mk (functorVertex c.val) :
      hoFunctor.obj ((ihom (join K (Δ[0] : SSet.{u}))).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex d.val)}
    (h : (hoFunctor.map (coconeRestriction K X)).toFunctor.map a =
      (hoFunctor.map (coconeRestriction K X)).toFunctor.map b) : a = b := by
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective _ _ a
  obtain ⟨f, rfl⟩ := homotopyCategory_homMk_surjective _ _ b
  simpa only [stableFunctorEdge_homotopy_roundtrip] using
    colimitCoconeHomotopy_homMk_eq c d hc hd
      (simplicialHomotopyOfFunctorEdge e) (simplicialHomotopyOfFunctorEdge f)
      (by simpa only [stableFunctorEdge_homotopy_roundtrip] using h)

/-- 概要：同型による形状の前合成は h 上でも忠実である。
方針：逆の前合成を備える単体集合の同型を h の圏同値に移す。
規約：値域への追加仮定は不要。使われ方：余錐表示から四角形に戻す。 -/
lemma stablePrecompIso_faithful {A B X : SSet.{u}} (e : A ≅ B) :
    (hoFunctor.map ((pre e.hom).app X)).toFunctor.Faithful := by
  let ei : (ihom B).obj X ≅ (ihom A).obj X := {
    hom := (pre e.hom).app X
    inv := (pre e.inv).app X
    hom_inv_id := by
      rw [← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id]
      rfl
    inv_hom_id := by
      rw [← NatTrans.comp_app, ← pre_map, e.hom_inv_id, pre_id]
      rfl }
  exact inferInstanceAs (Cat.equivOfIso (hoFunctor.mapIso ei)).functor.Faithful

/-- 概要：連続した二つの単体的な射による h の射の像は合成による像に一致する。
方針：射を辺で表し、二度の辺の像を計算する。
規約：始域は quasicategory。使われ方：複数の図式制限の照合。 -/
lemma stableHoMap_comp {A B C : SSet.{u}} [Quasicategory A] (i : A ⟶ B) (j : B ⟶ C)
    {x y : A _⦋0⦌} (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
    (hoFunctor.map j).toFunctor.map ((hoFunctor.map i).toFunctor.map f) =
      (hoFunctor.map (i ≫ j)).toFunctor.map f := by
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective x y f
  rfl

/-- 概要：等しい単体的な射による h の射の像は Arrow として等しい。
方針：射の等式で置き換える。
規約：端点の型の輸送も含む。使われ方：図式制限の厳密な等号の利用。 -/
lemma stableHoMap_congr_arrow {A B : SSet.{u}} {i j : A ⟶ B} (h : i = j)
    {x y : hoFunctor.obj A} (f : x ⟶ y) :
    Arrow.mk ((hoFunctor.map i).toFunctor.map f) =
      Arrow.mk ((hoFunctor.map j).toFunctor.map f) := by
  subst j
  rfl

/-- 概要：押し出し四角形間の任意の h の二射は span への制限が一致すれば等しい。
方針：余錐表示で図式への制限を比較し、形状の同型の忠実性で戻す。
規約：両端の四角形は押し出し。使われ方：cofiber 比較の合成。 -/
lemma pushoutSquare_hom_ext {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : IsPushoutSquare F) (hG : IsPushoutSquare G)
    {a b : (SSet.HomotopyCategory.mk (functorVertex F) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex G)}
    (h : (hoFunctor.map ((pre spanSquareBoundary).app X)).toFunctor.map a =
      (hoFunctor.map ((pre spanSquareBoundary).app X)).toFunctor.map b) : a = b := by
  have hf := stablePrecompIso_faithful (X := X) spanCoconeSquareIso
  apply hf.map_injective
  apply colimitCocone_hom_ext (pushoutCocone F) (pushoutCocone G) hF hG
  rw [stableHoMap_comp, stableHoMap_comp]
  have hi : (pre spanCoconeSquareIso.hom).app X ≫ coconeRestriction (horn 2 0 : SSet.{u}) X =
      (pre spanSquareBoundary).app X := by
    rw [coconeRestriction, ← NatTrans.comp_app, ← pre_map]
    rfl
  apply Arrow.mk_injective
  exact (stableHoMap_congr_arrow hi a).trans
    ((congrArg Arrow.mk h).trans (stableHoMap_congr_arrow hi b).symm)

/-- 概要：span への制限の後の始点評価は元の四角形の左下の評価に一致する。
方針：span の第一辺と四角形の下辺を照合し、零端点を計算する。
規約：厳密な単体的な射の等号。使われ方：始点成分の照合。 -/
lemma stableSpanPrecomp_sourceEvaluation (X : SSet.{u}) :
    (pre spanSquareBoundary).app X ≫ spanSourceEvaluation X =
      evaluateFunctorAt (Y := X)
        (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0) := by
  rw [spanSourceEvaluation_eq_evaluate, stable_pre_evaluateFunctorAt,
    ← SSet.yonedaEquiv_comp, Category.assoc, spanSquareBoundary_bottomEdge]
  congr 1
  apply Prod.ext <;> decide

/-- 概要：押し出し四角形から指定 suspension への二つの h の射は始点成分で決まる。
方針：span 比較の始点評価の単射性を、普遍余錐の射影の忠実性と合成する。
規約：始点成分は恒等射でなくてもよい。使われ方：接続射の合成と選択の比較。 -/
lemma cofiberSuspensionComparison_hom_ext {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : IsPushoutSquare F)
    {y : X _⦋0⦌} (s : SuspensionSquare y)
    {a b : (SSet.HomotopyCategory.mk (functorVertex F) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex s.square)}
    (h : (hoFunctor.map (evaluateFunctorAt (Y := X)
        (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0))).toFunctor.map a =
      (hoFunctor.map (evaluateFunctorAt (Y := X)
        (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0))).toFunctor.map b) : a = b := by
  apply pushoutSquare_hom_ext F s.square hF s.isPushout
  have hg₁ : IsTerminalVertex ((horn₂₀.ι₀₁ ≫ pushoutSpan s.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge]
    exact s.other_zero.2
  have hg₂ : IsTerminalVertex ((horn₂₀.ι₀₂ ≫ pushoutSpan s.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]
    exact s.zero_corner.2
  apply (spanSourceEvaluation_homMap_bijective (pushoutSpan F) (pushoutSpan s.square) hg₁ hg₂).1
  rw [stableHoMap_comp, stableHoMap_comp]
  apply Arrow.mk_injective
  exact (stableHoMap_congr_arrow (stableSpanPrecomp_sourceEvaluation X) a).trans
    ((congrArg Arrow.mk h).trans
      (stableHoMap_congr_arrow (stableSpanPrecomp_sourceEvaluation X) b).symm)

end SerrePositivity.InfinityCategories
