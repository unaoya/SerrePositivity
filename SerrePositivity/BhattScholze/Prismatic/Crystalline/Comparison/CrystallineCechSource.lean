module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta

/-!
# 結晶比較の完備自由 δ Čech 余脈体

## 概要
各 Čech 頂点に自由 δ 座標を置き、頂点の写像を完備自由 δ 環の射に延長する。

## 方針
完備自由 δ 環の普遍性で射を作り、恒等射と合成は初期座標で判定する。

## 規約
基底は生成元 p の結晶 prism。

## 使われ方
結晶比較の Frobenius 押し出しの下段。
-/

public noncomputable section

universe u

open CategoryTheory
open SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "Z" => (crystallineBasePrism p)
local notation "B" n => completedFreeDelta Z (AffineIndex r (SimplexCategory.len n))
local notation "D" n => completedFreeDeltaStructure Z (AffineIndex r (SimplexCategory.len n))
local notation "β" n => completedFreeDeltaBase Z (AffineIndex r (SimplexCategory.len n))
local notation "x" n => completedFreeDeltaVariable Z (AffineIndex r (SimplexCategory.len n))

/-- 頂点写像を自由座標の添字に作用させる。 -/
def crystallineCechIndexMap {m n : SimplexCategory} (θ : m ⟶ n) :
    AffineIndex.{u} r m.len → AffineIndex.{u} r n.len :=
  fun t => ⟨(t.down.1, θ.toOrderHom t.down.2)⟩

private theorem crystallineCechSourceMap_existsUnique {m n : SimplexCategory} (θ : m ⟶ n) :
    ∃! f : (B m) →+* (B n), (D m).IsDeltaHom (D n) f ∧
      f.comp (β m) = (β n) ∧ ∀ t, f ((x m) t) = (x n) (crystallineCechIndexMap r θ t) :=
  existsUnique_completedFreeDeltaHom Z (AffineIndex r m.len) (D n) (β n)
    (completedFreeDeltaBase_isDeltaHom Z (AffineIndex r n.len))
    (completedFreeDelta_complete_p Z (AffineIndex r n.len))
    (completedFreeDelta_complete_generator Z (AffineIndex r n.len))
    (fun t => (x n) (crystallineCechIndexMap r θ t))

/-- 頂点写像が誘導する完備自由 δ 環の射。 -/
def crystallineCechSourceMap {m n : SimplexCategory} (θ : m ⟶ n) :
    completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r m.len) →+*
      completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r n.len) :=
  (crystallineCechSourceMap_existsUnique p r θ).choose

theorem crystallineCechSourceMap_spec {m n : SimplexCategory} (θ : m ⟶ n) :
    (D m).IsDeltaHom (D n) (crystallineCechSourceMap.{u} p r θ) ∧
      (crystallineCechSourceMap.{u} p r θ).comp (β m) = (β n) ∧
      ∀ t, (crystallineCechSourceMap.{u} p r θ) ((x m) t) =
        (x n) (crystallineCechIndexMap r θ t) :=
  (crystallineCechSourceMap_existsUnique p r θ).choose_spec.1

/-- 結晶比較の完備自由 δ 環を台の余単体的可換環として読む。 -/
def crystallineCechSource : CosimplicialObject CommRingCat.{u} where
  obj n := CommRingCat.of (B n)
  map θ := CommRingCat.ofHom (crystallineCechSourceMap p r θ)
  map_id n := by
    obtain ⟨g, hg, hu⟩ := crystallineCechSourceMap_existsUnique.{u} p r (𝟙 n)
    apply CommRingCat.hom_ext
    change crystallineCechSourceMap p r (𝟙 n) = RingHom.id _
    refine (hu _ (crystallineCechSourceMap_spec p r _)).trans (hu _ ?_).symm
    exact ⟨(D n).isDeltaHom_id, RingHom.id_comp _, fun _ => rfl⟩
  map_comp {l m n} f g := by
    obtain ⟨h, _, hu⟩ := crystallineCechSourceMap_existsUnique.{u} p r (f ≫ g)
    apply CommRingCat.hom_ext
    change crystallineCechSourceMap p r (f ≫ g) =
      (crystallineCechSourceMap p r g).comp (crystallineCechSourceMap p r f)
    refine (hu _ (crystallineCechSourceMap_spec p r _)).trans (hu _ ?_).symm
    obtain ⟨hfδ, hfβ, hfx⟩ := crystallineCechSourceMap_spec.{u} p r f
    obtain ⟨hgδ, hgβ, hgx⟩ := crystallineCechSourceMap_spec.{u} p r g
    refine ⟨hgδ.comp hfδ, ?_, ?_⟩
    · rw [RingHom.comp_assoc, hfβ, hgβ]
    · intro t
      rw [RingHom.comp_apply, hfx, hgx]
      rfl

end SerrePositivity.BhattScholze.Prismatic
