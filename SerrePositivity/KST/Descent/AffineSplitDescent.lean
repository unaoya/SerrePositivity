module

public import SerrePositivity.KST.Descent.SectionedDescent
public import SerrePositivity.KST.Descent.AffineOrbitCovering

/-!
# 環の分裂からのアフィン射の全次数降下

## 概要
T →ₐ[A] A から Spec T → Spec A の実際の切断を構成し、切断つき降下を適用する。

## 方針
任意の固定した基底 S 上にアフィン対象を構成し、元の前層 L のまま比較する。

## 規約
基底変更に伴って前層を別の前層へ置き換えない。Noether 性は固定した S に課す。

## 使われ方
論文 補題 3.2・定理 3.1 の Čech 底変換後に分裂するアフィン射。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {A T : Type u} [CommRing A] [CommRing T]
variable [Algebra A T] [Algebra.FiniteType A T]

/-- 概要：固定した S 上の有限型アフィン対象（論文 §3）。
方針：指定された構造射をそのまま使う。
規約：構造射の有限型性を明示する。
使われ方：前層 L を同じ定義域内で基底変更後にも評価する。 -/
noncomputable def affineOverObject (a : Spec (.of A) ⟶ S)
    [LocallyOfFiniteType a] [QuasiCompact a] : FiniteTypeSchemes S :=
  ⟨Over.mk a, inferInstanceAs (LocallyOfFiniteType a), inferInstanceAs (QuasiCompact a)⟩

/-- 概要：有限型 A 代数を同じ S 上のアフィン対象にする（論文 §3）。
方針：Spec の構造射を a と合成する。
規約：S 上の前層の定義域を保持する。
使われ方：Čech 底変換後のテンソル積の対象。 -/
noncomputable def affineAlgebraOverObject (a : Spec (.of A) ⟶ S)
    [LocallyOfFiniteType a] [QuasiCompact a] : FiniteTypeSchemes S := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap A T))
  have : LocallyOfFiniteType p :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact ⟨Over.mk (p ≫ a), locallyOfFiniteType_comp p a, quasiCompact_comp p a⟩

/-- 概要：Spec T → Spec A を固定した有限型の圏内の射にする（論文 §3）。
方針：元の Spec の射を Over の射として包む。
規約：基底は S のまま。
使われ方：全次数降下の指定された幾何射。 -/
noncomputable def affineAlgebraOverProjection (a : Spec (.of A) ⟶ S)
    [LocallyOfFiniteType a] [QuasiCompact a] :
    affineAlgebraOverObject (T := T) a ⟶ affineOverObject a :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A T))))

omit [Algebra.FiniteType A T] in
/-- 概要：環の分裂が与える Spec の射は切断（論文 補題 3.2）。
方針：代数射の係数保存を Spec の反変性で移す。
規約：A 代数射 T → A を入力し、切断の等式を導出する。
使われ方：固定した S 上の切断の構成。 -/
theorem affineSplitSection_raw_identity (r : T →ₐ[A] A) :
    Spec.map (CommRingCat.ofHom r.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A T)) = 𝟙 (Spec (.of A)) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact r.commutes x

/-- 概要：環の分裂から固定した S 上の実際の切断（論文 補題 3.2）。
方針：Spec の切断の恒等式で構造射との可換性を検査する。
規約：切断そのものを有限型の圏内に構成する。
使われ方：完成した切断つき降下の適用。 -/
noncomputable def affineSplitSection (a : Spec (.of A) ⟶ S)
    [LocallyOfFiniteType a] [QuasiCompact a] (r : T →ₐ[A] A) :
    affineOverObject a ⟶ affineAlgebraOverObject (T := T) a :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom r.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom r.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap A T)) ≫ a) = a
    rw [← Category.assoc, affineSplitSection_raw_identity, Category.id_comp]))

/-- 概要：固定した S 上の切断の指定恒等式（論文 補題 3.2）。
方針：忘却して Spec の切断の等式を適用する。
規約：有限型の圏内の指定射との合成。
使われ方：全次数降下の切断の条件。 -/
theorem affineSplitSection_identity (a : Spec (.of A) ⟶ S)
    [LocallyOfFiniteType a] [QuasiCompact a] (r : T →ₐ[A] A) :
    affineSplitSection a r ≫ affineAlgebraOverProjection a = 𝟙 (affineOverObject a) := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact affineSplitSection_raw_identity r

variable {G : Type u} [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

/-- 概要：アフィン対象に元の環からの指定群作用を入れる（論文 定理 3.1）。
方針：Spec A 上の作用の等式を S への構造射と合成する。
規約：環の作用は Spec 上で逆元の comap により左作用へ移す。
使われ方：元の前層に対する固定部分の比較。 -/
noncomputable def affineAlgebraOverAction (a : Spec (.of A) ⟶ S)
    [LocallyOfFiniteType a] [QuasiCompact a] : G →* Aut (affineAlgebraOverObject (T := T) a) :=
  finiteTypeActionOfSchemeAction _ specAction (fun g ↦ by
    change (specAction (T := T) g).asIso.hom ≫
      (Spec.map (CommRingCat.ofHom (algebraMap A T)) ≫ a) = _
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ a) (specAction_over_base (A := A) g)))

/-- 概要：固定した S 上の作用は指定された射影の基底上にある（論文 (3.7)）。
方針：忘却して Spec A 上の元の作用の式を使う。
規約：S 上の圏内の射の等式。
使われ方：PiDescent の指定比較の定義。 -/
theorem affineAlgebraOverAction_over_base (a : Spec (.of A) ⟶ S)
    [LocallyOfFiniteType a] [QuasiCompact a] (g : G) :
    (affineAlgebraOverAction (T := T) a g).asIso.hom ≫ affineAlgebraOverProjection a =
      affineAlgebraOverProjection a := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact specAction_over_base g

/-- 概要：分裂するアフィン射の幾何的推移性から元の前層の全次数降下（論文 定理 3.1）。
方針：分裂から切断を構成し、既存の幾何的推移性を点の推移性へ移して適用する。
規約：作用・射・前層を変更せず、自然な列と有限積保存は実降下から供給すべき条件。
使われ方：Čech 底変換後に分裂した射の全係数・全整数次数の比較。 -/
theorem NaturalBlowupSequences.affine_split_piDescent [IsNoetherian S]
    {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [Nilinvariant S L]
    [∀ H n, PreservesFiniteProducts (L H n)] [Finite G]
    (a : Spec (.of A) ⟶ S) [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (r : T →ₐ[A] A) (transitive : IsGeometricallyTransitive A T G)
    (d : ℕ) (bound : topologicalKrullDim (Spec (.of A)) ≤ d) :
    L.PiDescent (affineAlgebraOverProjection (T := T) a) (affineAlgebraOverAction (G := G) a)
      (affineAlgebraOverAction_over_base a) := by
  have : IsSeparated (affineAlgebraOverObject (T := T) a).obj.hom :=
    inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap A T)) ≫ a))
  apply data.sectioned_piDescent (affineAlgebraOverProjection a) (affineAlgebraOverAction a)
    (affineAlgebraOverAction_over_base a) (affineSplitSection a r) (affineSplitSection_identity a r)
    _ d bound
  exact specAction_transitive_on_fibers transitive

end SerrePositivity.KST.Descent
