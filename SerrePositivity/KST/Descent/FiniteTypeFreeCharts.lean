module

public import SerrePositivity.KST.Descent.FiniteFlatFiniteFreeCover
public import SerrePositivity.KST.Descent.BlowupGeometry

/-!
# 有限自由アフィンチャートを元の有限型の圏へ持ち上げる

## 概要
構成した有限自由チャートの四つの射を、元の前層の定義域内の実際の Cartesian 正方形にする。

## 方針
基底と始域の開包含による有限型性を使い、スキームの Cartesian 性を忘却関手で反映する。

## 規約
基底 S の Noether 性を明示する。実際の代数と正の有限基底は変更しない。

## 使われ方
論文 補題 3.2 の有限平坦 transfer と、元の前層に対する Zariski Čech の局所自明化。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module

namespace SerrePositivity.KST.Descent.FiniteFreeAffineChart

/-- 概要：自由チャートの元の始域への射も開埋め込み（論文 補題 3.2）。
方針：基底の開包含を実際の Cartesian 正方形で底変換する。
規約：始域の位相だけを比較する主張ではない。
使われ方：チャートの始域を元の有限型の圏へ持ち上げる。 -/
theorem sourceMap_isOpenImmersion {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : FiniteFreeAffineChart f) : IsOpenImmersion c.sourceMap :=
  MorphismProperty.of_isPullback c.cartesian.flip c.openImmersion

/-- 概要：有限自由チャートの実際の構造射の rank は指定した基底の本数（補題 3.2）。
方針：基底から有限自由性を供給し、Spec の rank と stalk rank の公式を使う。
規約：チャート基礎環の非零性は評価する点から得る。
使われ方：局所自明化の rank と実際の射の rank の整合性。 -/
theorem rank_at_point {X Y : Scheme.{u}} {f : X ⟶ Y} (c : FiniteFreeAffineChart f)
    (y : Spec c.baseRing) :
    letI : Algebra c.baseRing c.sourceRing := c.algebra
    (Spec.map (CommRingCat.ofHom (algebraMap c.baseRing c.sourceRing))).finrank y = c.rank := by
  let : Algebra c.baseRing c.sourceRing := c.algebra
  have : Nontrivial c.baseRing := y.nontrivial
  have : Module.Free c.baseRing c.sourceRing := Module.Free.of_basis c.basis
  have : Module.Finite c.baseRing c.sourceRing := Module.Finite.of_basis c.basis
  have : Module.Flat c.baseRing c.sourceRing := inferInstance
  calc
    _ = Module.rankAtStalk c.sourceRing y :=
      Scheme.Hom.finrank_SpecMap_algebraMap c.baseRing c.sourceRing y
    _ = Module.finrank c.baseRing c.sourceRing :=
      congrFun (Module.rankAtStalk_eq_finrank_of_free (R := c.baseRing) (M := c.sourceRing)) y
    _ = c.rank := by simpa using Module.finrank_eq_nat_card_basis c.basis

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) (c : FiniteFreeAffineChart f.hom.left)

/-- 概要：有限自由チャートの基底を元の有限型の圏へ持ち上げる（補題 3.2）。
方針：基底への開包含と元の構造射を合成する。
規約：underlying scheme は元の Spec baseRing。
使われ方：同じ前層 L をチャートで評価する。 -/
noncomputable def toBaseObject : FiniteTypeSchemes S := by
  have := c.openImmersion
  have : LocallyOfFiniteType Y.obj.hom := Y.property.1
  have : QuasiCompact Y.obj.hom := Y.property.2
  exact ⟨Over.mk (c.baseMap ≫ Y.obj.hom), locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：有限自由チャートの始域を元の有限型の圏へ持ち上げる（補題 3.2）。
方針：始域への開包含と元の構造射を合成する。
規約：underlying scheme は正の有限基底を持つ元の Spec sourceRing。
使われ方：実際の有限平坦 transfer の始域。 -/
noncomputable def toSourceObject : FiniteTypeSchemes S := by
  have := c.sourceMap_isOpenImmersion
  have : LocallyOfFiniteType X.obj.hom := X.property.1
  have : QuasiCompact X.obj.hom := X.property.2
  exact ⟨Over.mk (c.sourceMap ≫ X.obj.hom), locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：元の有限型の圏内のチャートの基底包含（論文 補題 3.2）。
方針：実際の baseMap を基底 S 上の射へ持ち上げる。
規約：underlying scheme の射を変更しない。
使われ方：Zariski 被覆の指定射。 -/
noncomputable def toBaseInclusion : c.toBaseObject f ⟶ Y :=
  ObjectProperty.homMk (Over.homMk c.baseMap)

/-- 概要：元の有限型の圏内のチャートの始域包含（論文 補題 3.2）。
方針：実際の sourceMap を基底 S 上の射へ持ち上げる。
規約：underlying scheme の射を変更しない。
使われ方：底変換の指定第一射影。 -/
noncomputable def toSourceInclusion : c.toSourceObject f ⟶ X :=
  ObjectProperty.homMk (Over.homMk c.sourceMap)

/-- 概要：有限自由チャートの実際の構造射を元の有限型の圏へ持ち上げる（補題 3.2）。
方針：Cartesian 正方形の可換式と元の S 上の可換式を合成する。
規約：実際の代数構造による Spec 射影を使う。
使われ方：同じ前層の自然な transfer の対象。 -/
noncomputable def toProjection : c.toSourceObject f ⟶ c.toBaseObject f := by
  let : Algebra c.baseRing c.sourceRing := c.algebra
  refine ObjectProperty.homMk (Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap c.baseRing c.sourceRing))) ?_)
  change Spec.map (CommRingCat.ofHom (algebraMap c.baseRing c.sourceRing)) ≫
    (c.baseMap ≫ Y.obj.hom) = c.sourceMap ≫ X.obj.hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Y.obj.hom) c.cartesian.w.symm).trans
      ((Category.assoc _ _ _).trans (congrArg (c.sourceMap ≫ ·) f.hom.w)))

/-- 概要：有限型の圏内の指定四辺は可換（論文 補題 3.2）。
方針：二つの忘却関手の射の単射性で元の Cartesian 正方形の式に戻す。
規約：同じ基底 S 上の等式。
使われ方：実際の引き戻しへの比較射と前層の自然性。 -/
theorem toProjection_comm :
    c.toSourceInclusion f ≫ f = c.toProjection f ≫ c.toBaseInclusion f := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact c.cartesian.w

/-- 概要：自由チャートの正方形は元の有限型の圏内でも実際の引き戻し（補題 3.2）。
方針：元のスキームの Cartesian 性を Over と充満部分圏の忘却で反映する。
規約：指定四辺と元の前層の定義域を保持する。
使われ方：Zariski Čech と有限平坦 transfer に同じ底変換を渡す。 -/
theorem toProjection_isPullback :
    IsPullback (c.toSourceInclusion f) (c.toProjection f) f (c.toBaseInclusion f) := by
  let F := ObjectProperty.ι
    (fun X : Over S ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom) ⋙ Over.forget S
  exact c.cartesian.of_map F (c.toProjection_comm f)

/-- 概要：元の有限忠実平坦有限表示射の自由チャートの射影も同じ性質（補題 3.2）。
方針：実際の Cartesian 正方形で四つの性質を底変換する。
規約：対象と射を元の有限型の圏内に保つ。
使われ方：実際の前層の有限平坦 transfer の適用。 -/
theorem toProjection_flatCover [IsFinite f.hom.left] [AlgebraicGeometry.Flat f.hom.left]
    [Surjective f.hom.left] [LocallyOfFinitePresentation f.hom.left] :
    IsFinite (c.toProjection f).hom.left ∧ AlgebraicGeometry.Flat (c.toProjection f).hom.left ∧
      Surjective (c.toProjection f).hom.left ∧
      LocallyOfFinitePresentation (c.toProjection f).hom.left :=
  ⟨MorphismProperty.of_isPullback c.cartesian inferInstance,
    MorphismProperty.of_isPullback c.cartesian inferInstance,
    MorphismProperty.of_isPullback c.cartesian inferInstance,
    MorphismProperty.of_isPullback c.cartesian inferInstance⟩

/-- 概要：有限型の圏内の自由射影の実際の rank も指定した基底の本数（補題 3.2）。
方針：同じ underlying scheme の構造射の rank の公式を使う。
規約：群ごとの比較や Tot についての主張は含めない。
使われ方：有限基底と局所 transfer の rank の一致。 -/
theorem toProjection_rank (y : (c.toBaseObject f).obj.left) :
    (c.toProjection f).hom.left.finrank y = c.rank := c.rank_at_point y

/-- 概要：自由チャートの始域と指定された元の有限型の圏の引き戻しの同型（補題 3.2）。
方針：同じ Cartesian 正方形を表す二つの標準同型を合成する。
規約：元の前層が使う指定引き戻しを変更しない。
使われ方：有限自由な代数表示を実際の底変換被覆へ移す。 -/
noncomputable def toPullbackIso :
    c.toSourceObject f ≅ finiteTypePullback f (c.toBaseInclusion f) :=
  (c.toProjection_isPullback f).isoPullback ≪≫
    (finiteTypePullback_isPullback f (c.toBaseInclusion f)).isoPullback.symm

/-- 概要：指定引き戻しとの同型は基底チャートへの射影を保つ（補題 3.2）。
方針：標準同型の第二射影の公式を合成する。
規約：同じ toProjection そのものとの等式。
使われ方：実際の transfer と Čech の底変換に同じ射を渡す。 -/
theorem toPullbackIso_hom_snd :
    (c.toPullbackIso f).hom ≫ finiteTypePullbackSnd f (c.toBaseInclusion f) =
      c.toProjection f :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (finiteTypePullback_isPullback f
      (c.toBaseInclusion f)).isoPullback_inv_snd).trans
        (c.toProjection_isPullback f).isoPullback_hom_snd)

/-- 概要：指定引き戻しとの同型は元の始域への射影を保つ（補題 3.2）。
方針：標準同型の第一射影の公式を合成する。
規約：同じ toSourceInclusion そのものとの等式。
使われ方：元の前層の引き戻し比較の同一性を保持する。 -/
theorem toPullbackIso_hom_fst :
    (c.toPullbackIso f).hom ≫ finiteTypePullbackFst f (c.toBaseInclusion f) =
      c.toSourceInclusion f :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (finiteTypePullback_isPullback f
      (c.toBaseInclusion f)).isoPullback_inv_fst).trans
        (c.toProjection_isPullback f).isoPullback_hom_fst)

end SerrePositivity.KST.Descent.FiniteFreeAffineChart

namespace SerrePositivity.KST.Descent

/-- 概要：有限自由な有限開被覆は元の有限型の圏の基底包含でも全体を覆う（補題 3.2）。
方針：実際の有限部分被覆の点の持ち上げを同じ underlying scheme の射へ移す。
規約：全てのチャートは同じ S 上有限型。有限添字型は元の有限集合。
使われ方：Zariski Čech 降下と、各チャートの有限平坦 transfer の合成。 -/
theorem finiteTypeFreeCharts_covers {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSchemes S} (f : X ⟶ Y)
    [IsFinite f.hom.left] [AlgebraicGeometry.Flat f.hom.left] [Surjective f.hom.left]
    [LocallyOfFinitePresentation f.hom.left] (y : Y.obj.left) :
    ∃ i : finiteFreeChartIndices f.hom.left,
      let c := finiteFreeChartFamily f.hom.left i.val
      ∃ z : (c.toBaseObject f).obj.left, (c.toBaseInclusion f).hom.left z = y :=
  finiteFreeChartIndices_covers f.hom.left y

end SerrePositivity.KST.Descent
