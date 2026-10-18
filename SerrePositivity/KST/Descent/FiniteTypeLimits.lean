module

public import SerrePositivity.KST.Descent.NoetherianReduction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Noether 基底上の有限型の圏の有限極限

## 概要
前層 L の定義域内で、実際の Čech nerve を作るための有限極限を構成する。

## 方針
有限型対象間の射の局所有限型性と Noether 性による準コンパクト性を使う。
スキームの引き戻しを Over に持ち上げ、忘却による極限の反映を適用する。

## 規約
基底 S の Noether 性を明示する。これは幾何の通常の極限であり、Tot ではない。

## 使われ方
論文 補題 3.2 の τ 位相の層論を Čech 計算に置換する際の幾何的な図式。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}}

/-- 概要：有限型対象間の射は局所有限型（論文 §3）。
方針：基底への合成が局所有限型であることから導く。
規約：Noether 性はこの性質には不要。
使われ方：実際の引き戻しの有限型性。 -/
theorem finiteTypeMorphism_locallyOfFiniteType {X Y : FiniteTypeSchemes S} (f : X ⟶ Y) :
    LocallyOfFiniteType f.hom.left := by
  have h : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) :=
    f.hom.w.symm ▸ X.property.1
  exact locallyOfFiniteType_of_comp f.hom.left Y.obj.hom

/-- 概要：固定した基底自身を有限型の圏の対象にする（論文 §3）。
方針：構造射を恒等射とする。
規約：基底を変更しない。
使われ方：幾何的な終対象と有限極限。 -/
def finiteTypeBaseObject (S : Scheme.{u}) : FiniteTypeSchemes S :=
  ⟨Over.mk (𝟙 S), inferInstanceAs (LocallyOfFiniteType (𝟙 S)),
    inferInstanceAs (QuasiCompact (𝟙 S))⟩

/-- 概要：基底自身は有限型の圏の終対象（論文 §3）。
方針：構造射を一意な射として持ち上げる。
規約：任意の有限型対象に対する普遍性。
使われ方：Čech の幾何的な有限極限。 -/
def finiteTypeBaseIsTerminal : IsTerminal (finiteTypeBaseObject S) :=
  IsTerminal.ofUniqueHom
    (fun X ↦ ObjectProperty.homMk (Over.homMk X.obj.hom (by simp [finiteTypeBaseObject])))
    (fun X f ↦ by
      apply ObjectProperty.hom_ext
      apply (Over.forget S).map_injective
      change f.hom.left = X.obj.hom
      exact (Category.comp_id f.hom.left).symm.trans f.hom.w)

variable [IsNoetherian S] {X Y Z : FiniteTypeSchemes S}

/-- 概要：Noether 基底上の実際の引き戻しを有限型の圏内へ持ち上げる（論文 補題 3.2）。
方針：射の局所有限型性と Noether な始域からの準コンパクト性を底変換する。
規約：対象の underlying scheme は Mathlib の実際の引き戻し。
使われ方：Čech nerve の各段を元の前層の定義域に構成する。 -/
noncomputable def finiteTypePullback (f : Y ⟶ X) (g : Z ⟶ X) : FiniteTypeSchemes S := by
  have : LocallyOfFiniteType g.hom.left := finiteTypeMorphism_locallyOfFiniteType g
  have : LocallyOfFiniteType Y.obj.hom := Y.property.1
  have : QuasiCompact Y.obj.hom := Y.property.2
  exact ⟨Over.mk (pullback.fst f.hom.left g.hom.left ≫ Y.obj.hom),
    locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：実際の引き戻しの第一射影を有限型の圏へ持ち上げる（論文 補題 3.2）。
方針：構造射を第一射影で定義したことを使う。
規約：元の射影を変更しない。
使われ方：Čech 底変換の指定比較。 -/
noncomputable def finiteTypePullbackFst (f : Y ⟶ X) (g : Z ⟶ X) :
    finiteTypePullback f g ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.fst f.hom.left g.hom.left))

/-- 概要：実際の引き戻しの第二射影を有限型の圏へ持ち上げる（論文 補題 3.2）。
方針：引き戻しの可換性と二つの構造射の等式を使う。
規約：元の射影を変更しない。
使われ方：Čech 底変換の指定比較。 -/
noncomputable def finiteTypePullbackSnd (f : Y ⟶ X) (g : Z ⟶ X) :
    finiteTypePullback f g ⟶ Z :=
  ObjectProperty.homMk (Over.homMk (pullback.snd f.hom.left g.hom.left) (by
    change pullback.snd f.hom.left g.hom.left ≫ Z.obj.hom =
      pullback.fst f.hom.left g.hom.left ≫ Y.obj.hom
    rw [← g.hom.w, ← Category.assoc, ← pullback.condition, Category.assoc, f.hom.w]))

/-- 概要：有限型の圏内で引き戻しの正方形は可換（論文 補題 3.2）。
方針：忘却後に元の引き戻しの可換性を使う。
規約：指定二射影の等式。
使われ方：極限の反映。 -/
theorem finiteTypePullback_comm (f : Y ⟶ X) (g : Z ⟶ X) :
    finiteTypePullbackFst f g ≫ f = finiteTypePullbackSnd f g ≫ g := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact pullback.condition

/-- 概要：構成した対象は有限型の圏内でも実際の引き戻し（論文 補題 3.2）。
方針：Over と充満部分圏の忘却による極限の反映を使う。
規約：元の前層を適用できる圏内での普遍性。
使われ方：Čech の図式とその分裂データ。 -/
theorem finiteTypePullback_isPullback (f : Y ⟶ X) (g : Z ⟶ X) :
    IsPullback (finiteTypePullbackFst f g) (finiteTypePullbackSnd f g) f g := by
  let F := ObjectProperty.ι
    (fun X : Over S ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom) ⋙ Over.forget S
  exact (IsPullback.of_hasPullback f.hom.left g.hom.left).of_map F (finiteTypePullback_comm f g)

/-- 概要：Noether 基底上有限型の圏は有限極限を持つ（論文 補題 3.2）。
方針：構成した終対象と全ての引き戻しから有限極限を得る。
規約：通常の幾何的極限の存在であり、値域のホモトピー極限の仮定ではない。
使われ方：元の L の定義域内での実際の Čech nerve。 -/
noncomputable instance finiteTypeSchemes_hasFiniteLimits :
    HasFiniteLimits (FiniteTypeSchemes S) := by
  let : HasTerminal (FiniteTypeSchemes S) := finiteTypeBaseIsTerminal.hasTerminal
  let {X Y Z : FiniteTypeSchemes S} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
    (finiteTypePullback_isPullback f g).hasPullback
  let : HasPullbacks (FiniteTypeSchemes S) := hasPullbacks_of_hasLimit_cospan _
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

end SerrePositivity.KST.Descent
