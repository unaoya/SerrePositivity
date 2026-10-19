module
public import SerrePositivity.KST.SConstruction.SurjectiveBaseChangeDetection
public import SerrePositivity.KST.SConstruction.BaseChangeMapNaturality

/-! # 連結基底上の非空な任意の基底変換による同値検出
概要：連結な Kan 基底上の二つの Kan fibration の間の射は、非空な任意の基底変換で同値を検出できる。
方針：基底変換射を anodyne・Kan に分解し、両構造射の right properness と全単体全射性を使う。
規約：基底変換元に Kan 性を要求しない。使われ方：退化から残る δ₀ の面条件を検出する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomotopicalAlgebra SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 連結な Kan 基底の二つの Kan fibration の間の射の同値は非空な任意の基底変換で検出できる。 -/
lemma localized_isIso_of_connected_baseChange {E B : SSet.{u}}
    [KanComplex B] [SSet.IsPreconnected B] (t : E ⟶ B) (e : E _⦋0⦌)
    {X Y : Over B} (f : X ⟶ Y) (hX : J.rlp X.hom) (hY : J.rlp Y.hom)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor t).map f))) :
    IsIso (AnodyneHomotopy.anodyneQ.map f.left) := by
  let Q := AnodyneHomotopy.anodyneQ
  let d := AnodyneKanReplacement.factorization.factorizationData t
  have hi : IsIso (Q.map d.i) := (Localization.inverts Q anodyneExtensions) d.i d.hi
  have hiX : IsIso (Q.map (pullbackMapBase t d.p X.hom d.i d.fac)) :=
    pullbackMapBase_localized_isIso_of_fibration t d.p X.hom hX d.i d.fac hi
  have hiY : IsIso (Q.map (pullbackMapBase t d.p Y.hom d.i d.fac)) :=
    pullbackMapBase_localized_isIso_of_fibration t d.p Y.hom hY d.i d.fac hi
  have hp : IsIso (Q.map ((sliceFiberFunctor d.p).map f)) := by
    have he := congrArg Q.map (pullbackMapBase_slice_naturality t d.p d.i d.fac f)
    rw [Q.map_comp, Q.map_comp] at he
    have hc : IsIso (Q.map (pullbackMapBase t d.p X.hom d.i d.fac) ≫
        Q.map ((sliceFiberFunctor d.p).map f)) := he ▸ inferInstance
    exact (isIso_comp_left_iff _ _).mp hc
  let : Fibration d.p := (SSet.modelCategoryQuillen.fibration_iff _).mpr d.hp
  let : KanComplex d.Z := isFibrant_of_fibration d.p
  let : Fibration Y.hom := (SSet.modelCategoryQuillen.fibration_iff _).mpr hY
  let : KanComplex Y.left := isFibrant_of_fibration Y.hom
  exact localized_isIso_of_connected_fibration_baseChange d.p (d.i.app _ e) f hp

end SerrePositivity.KST.SConstruction
