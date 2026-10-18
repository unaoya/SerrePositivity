module

public import SerrePositivity.KST.Descent.FiniteTypeGeneralBaseChange
public import SerrePositivity.KST.Descent.GeneralFiniteDimension
public import SerrePositivity.KST.Descent.SectionedDescent

/-!
# 一般の基底変更で切断を持つ射の全次数降下

## 概要
非アフィンな基底への指定底変換にも、元の環の幾何的推移性から切断つき降下を適用する。

## 方針
元の射への持ち上げから切断を作り、任意の底変換での推移性と一般の有限次元上界を渡す。

## 規約
自然な blowup 列・有限積保存・冪零不変性は実降下から供給すべき条件のまま明示する。

## 使われ方
論文 補題 3.2・3.3 の混合 Čech の各段。
原典の τ 位相の層論を Tot の Fubini・分裂降下・細分の Čech 計算へ置換する段階。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：有限型の圏の指定引き戻しの始域は基底上で分離的（論文 補題 3.3）。
方針：忘却が保つ Cartesian 正方形から第二射影の分離性を得て、構造射と合成する。
規約：始域のアフィン性を用いない。使われ方：一般の基底変更への切断つき降下。 -/
theorem finiteTypePullback_isSeparated {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSchemes S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f.hom.left] [IsSeparated Z.obj.hom] :
    IsSeparated (pullback f g).obj.hom := by
  let F := finiteTypeSchemesForget S
  have H : IsPullback (F.map (pullback.fst f g)) (F.map (pullback.snd f g))
      (F.map f) (F.map g) := (IsPullback.of_hasPullback f g).map F
  have : IsSeparated (pullback.snd f g).hom.left :=
    MorphismProperty.of_isPullback H (inferInstanceAs (IsSeparated f.hom.left))
  have h : IsSeparated ((pullback.snd f g).hom.left ≫ Z.obj.hom) := inferInstance
  exact (pullback.snd f g).hom.w ▸ h

variable {S : Scheme.{u}} [IsNoetherian S] {A T G : Type u}
  [CommRing A] [CommRing T] [Algebra A T] [Algebra.FiniteType A T]
  [Group G] [MulSemiringAction G T] [SMulCommClass G A T]
variable (a : Spec (.of A) ⟶ S) [LocallyOfFiniteType a] [QuasiCompact a]
  {Z : FiniteTypeSchemes S} (k : Z ⟶ affineOverObject a)

local notation "p" => affineAlgebraOverProjection (T := T) a
local notation "act" => affineFiniteTypeBaseChangeAction (T := T) (G := G) a k

/-- 概要：指定底変換の作用は第二射影の基底上にある（論文 (3.7)）。
方針：指定 pullbackAction の第二射影の公式を使う。
規約：作用も射も元の有限型の圏内。使われ方：不変部分への指定比較。 -/
theorem finiteTypeBaseChangeAction_over_base (g : G) :
    (act g).asIso.hom ≫ pullback.snd p k = pullback.snd p k := by
  exact (pullbackAction_snd p k (affineAlgebraOverAction (G := G) a) 1 1 _ _ g).trans
    (Category.comp_id _)

/-- 概要：元の射への持ち上げから指定底変換の切断を構成する（論文 補題 3.2）。
方針：持ち上げと恒等射を引き戻しの普遍性へ入れる。
規約：選択された引き戻しをそのまま使う。使われ方：混合 Čech の分裂行。 -/
noncomputable def finiteTypeBaseChangeSection (s : Z ⟶ affineAlgebraOverObject (T := T) a)
    (hs : s ≫ p = k) : Z ⟶ pullback p k :=
  pullback.lift s (𝟙 Z) (hs.trans (Category.id_comp k).symm)

/-- 概要：構成した射は指定第二射影の切断（論文 補題 3.2）。
方針：引き戻しの第二射影の公式を評価する。
規約：切断性を追加仮定にしない。使われ方：切断つき次元帰納への入力。 -/
theorem finiteTypeBaseChangeSection_identity (s : Z ⟶ affineAlgebraOverObject (T := T) a)
    (hs : s ≫ p = k) : finiteTypeBaseChangeSection a k s hs ≫ pullback.snd p k = 𝟙 Z :=
  pullback.lift_snd _ _ _

/-- 概要：一般の基底変更で持ち上げがあれば指定比較は全次数同型（論文 補題 3.2・3.3）。
方針：一般の推移性・分離性・構成した切断を有限次元の帰納へ渡す。
規約：自然な列・積保存・冪零不変性は実降下に由来すべき条件として明示する。
使われ方：非アフィンな blowup 上も含む混合 Čech の各段。 -/
theorem NaturalBlowupSequences.generalBaseChange_piDescent
    {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [Nilinvariant S L]
    [∀ H n, PreservesFiniteProducts (L H n)] [Finite G] [IsSeparated Z.obj.hom]
    (s : Z ⟶ affineAlgebraOverObject (T := T) a) (hs : s ≫ p = k)
    (transitive : IsGeometricallyTransitive A T G)
    (d : ℕ) (bound : topologicalKrullDim Z.obj.left ≤ d) :
    L.PiDescent (pullback.snd p k) act (finiteTypeBaseChangeAction_over_base a k) := by
  have : IsSeparated (affineAlgebraOverProjection (T := T) a).hom.left := inferInstanceAs
    (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap A T))))
  have : IsSeparated (pullback p k).obj.hom := finiteTypePullback_isSeparated p k
  exact data.sectioned_piDescent (pullback.snd p k) act
    (finiteTypeBaseChangeAction_over_base a k)
    (finiteTypeBaseChangeSection a k s hs) (finiteTypeBaseChangeSection_identity a k s hs)
    (finiteTypeBaseChange_transitive a k transitive) d bound

/-- 概要：局所 Noether 基底では一般の分裂底変換の全次数降下に次元仮定は不要（定理 3.1）。
方針：指定された基底射から有限次元上界を導き、一般の切断つき底変換へ適用する。
規約：自然な列・積保存・冪零不変性の条件は同じであり、定理 3.1 全体の完成ではない。
使われ方：blowup と閉中心を含む分裂した底変換の比較。 -/
theorem NaturalBlowupSequences.localNoether_generalBaseChange_piDescent
    [IsNoetherianRing A] [IsLocalRing A] {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [Nilinvariant S L]
    [∀ H n, PreservesFiniteProducts (L H n)] [Finite G] [IsSeparated Z.obj.hom]
    (s : Z ⟶ affineAlgebraOverObject (T := T) a) (hs : s ≫ p = k)
    (transitive : IsGeometricallyTransitive A T G) :
    L.PiDescent (pullback.snd p k) act (finiteTypeBaseChangeAction_over_base a k) := by
  have hFinite : LocallyOfFiniteType k.hom.left := finiteTypeMorphism_locallyOfFiniteType k
  obtain ⟨d, bound⟩ := @localNoether_schemeMorphism_dimension_bound A _ _ _
    Z.obj.left inferInstance k.hom.left hFinite
  exact data.generalBaseChange_piDescent a k s hs transitive d bound

end SerrePositivity.KST.Descent
