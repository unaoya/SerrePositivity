module

public import SerrePositivity.KST.Descent.FiniteTypeAffineTensorSquare
public import SerrePositivity.KST.Descent.FiniteTypeLimits
public import SerrePositivity.KST.Descent.EquivariantPullbackComparison

/-!
# 指定された実際のアフィン引き戻しの降下

## 概要
テンソル積モデルの全次数降下を、有限型の圏の指定引き戻しの第一射影へ移す。

## 方針
二射影を保つ標準同型の同変性を証明し、元の前層の指定比較の自然性を使う。

## 規約
引き戻しの作用は既存の pullbackAction。対象同型だけで作用の比較を省略しない。

## 使われ方
論文 補題 3.2 の Čech 計算でのアフィン底変換と切断つき降下の接続。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {A B T : Type u}
  [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T]
  [Algebra.FiniteType A B] [Algebra.FiniteType A T]
variable (a : Spec (.of A) ⟶ S) [LocallyOfFiniteType a] [QuasiCompact a]

/-- 概要：テンソル積モデルと指定引き戻しの標準同型（論文 補題 3.2）。
方針：有限型の圏内で証明した Cartesian 性の普遍性を使う。
規約：二射影との合成公式を持つ指定同型。
使われ方：元の L の評価と不変部分の比較。 -/
noncomputable def affineTensorPullbackIso : affineTensorObject (B := B) (T := T) a ≅
    pullback (affineAlgebraOverProjection (T := B) a)
      (affineAlgebraOverProjection (T := T) a) :=
  (affineTensorSquare_isPullback (B := B) (T := T) a).isoPullback

variable {G : Type u} [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

/-- 概要：実際のアフィン引き戻しへの指定作用（論文 補題 3.2）。
方針：左因子と基底を自明作用とし、右因子に元の作用を使う。
規約：テンソル積モデルから共役で作用を定義しない。
使われ方：Čech 底変換の指定比較の終域。 -/
noncomputable def affinePullbackAction : G →* Aut
    (pullback (affineAlgebraOverProjection (T := B) a)
      (affineAlgebraOverProjection (T := T) a)) :=
  pullbackAction _ _ 1 (affineAlgebraOverAction (G := G) a) 1
    (fun _ ↦ by simp) (fun g ↦ by simpa using affineAlgebraOverAction_over_base a g)

/-- 概要：指定引き戻しの第一射影は基底上の作用を持つ（論文 補題 3.2）。
方針：引き戻し作用の第一射影との合成公式を使う。
規約：左因子の作用は自明。
使われ方：元の L の PiDescent の指定射。 -/
theorem affinePullbackAction_over_base (g : G) :
    (affinePullbackAction (B := B) (T := T) a g).asIso.hom ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  exact (pullbackAction_fst _ _ 1 (affineAlgebraOverAction (G := G) a) 1 _ _ g).trans
    (Category.comp_id _)

/-- 概要：テンソル積から指定引き戻しへの同型は指定作用と同変（論文 補題 3.2）。
方針：モデルの二射影の同変性を、Cartesian 比較の一般補題に渡す。
規約：同型は二射影を保つ標準比較そのもの。
使われ方：実際の指定降下比較の同型性の移行。 -/
theorem affineTensorPullbackIso_equivariant (g : G) :
    (affineTensorAction (B := B) (T := T) a g).asIso.hom ≫
        (affineTensorPullbackIso (B := B) (T := T) a).hom =
      (affineTensorPullbackIso (B := B) (T := T) a).hom ≫
        (affinePullbackAction (B := B) (T := T) a g).asIso.hom := by
  exact isPullback_isoPullback_equivariant (affineTensorSquare_isPullback a)
    (affineTensorAction a) 1 (affineAlgebraOverAction a) 1 (fun _ ↦ by simp)
    (fun g ↦ by simpa using affineAlgebraOverAction_over_base a g)
    (fun g ↦ (affineTensorAction_over_base a g).trans (Category.comp_id _).symm)
    (affineTensorSnd_equivariant a) g

/-- 概要：指定されたアフィン引き戻しの第一射影の全次数降下（論文 補題 3.2）。
方針：同変な標準同型による指定比較の自然性でモデルの降下を移す。
規約：元の S 上の L と指定 pullbackAction を保持し、実降下の帰結の条件を明示する。
使われ方：Čech の底変換の射への全係数・全整数次数の比較。 -/
theorem NaturalBlowupSequences.affine_pullback_piDescent
    {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [Nilinvariant S L]
    [∀ H n, PreservesFiniteProducts (L H n)] [Finite G] [IsSeparated a]
    (φ : T →ₐ[A] B) (transitive : IsGeometricallyTransitive A T G)
    (d : ℕ) (bound : topologicalKrullDim (Spec (.of B)) ≤ d) :
    L.PiDescent (pullback.fst (affineAlgebraOverProjection (T := B) a)
      (affineAlgebraOverProjection (T := T) a)) (affinePullbackAction (G := G) a)
      (affinePullbackAction_over_base a) := by
  apply (L.piDescent_iff_of_bijective_square _ (affineTensorFst a)
    (affineTensorPullbackIso a).hom (𝟙 _) _ (affinePullbackAction a) (affineTensorAction a)
    (affinePullbackAction_over_base a) (affineTensorAction_over_base a)
    (affineTensorPullbackIso_equivariant a) _ _).mpr
    (data.affineTensorFst_piDescent a φ transitive d bound)
  · exact (affineTensorSquare_isPullback a).isoPullback_hom_fst.trans
      (Category.comp_id _).symm
  · intro H n
    exact ConcreteCategory.bijective_of_isIso ((L H n).map (affineTensorPullbackIso a).hom.op)
  · intro H n
    exact ConcreteCategory.bijective_of_isIso ((L H n).map (𝟙 _).op)

end SerrePositivity.KST.Descent
