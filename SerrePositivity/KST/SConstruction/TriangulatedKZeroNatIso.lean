module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroEquiv

/-! # 三角圏 K₀ 比較の自然同型
概要：対象類を保つ零次 K 群の同型を可換群値の自然同型に束ねる。
方針：完全関手の誘導準同型の恒等・合成則を対象類で検証する。
規約：スペクトル値の coherent 関手性とは区別する。
使われ方：L1e の自然な π₀ K = K₀ 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 完全関手の三角圏 K₀ への作用は恒等を保つ。 -/
lemma triangulatedKZeroSourceMap_id (X : StableModel.{u}) :
    triangulatedKZeroSourceMap (𝟙 X) = AddMonoidHom.id _ := by
  apply TriangulatedK0.hom_ext
  intro a
  rw [triangulatedKZeroSourceMap_mk]
  rfl

/-- 完全関手の三角圏 K₀ への作用は合成を保つ。 -/
lemma triangulatedKZeroSourceMap_comp {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    triangulatedKZeroSourceMap (f ≫ g) =
      (triangulatedKZeroSourceMap g).comp (triangulatedKZeroSourceMap f) := by
  apply TriangulatedK0.hom_ext
  intro a
  simp only [AddMonoidHom.comp_apply, triangulatedKZeroSourceMap_mk]
  rfl

/-- 小さい安定圏のホモトピー圏の三角圏 K₀ の関手。 -/
def triangulatedKZeroFunctor : StableModel.{u} ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (TriangulatedK0 (hoFunctor.obj X.carrier))
  map f := AddCommGrpCat.ofHom (triangulatedKZeroSourceMap f)
  map_id X := congrArg AddCommGrpCat.ofHom (triangulatedKZeroSourceMap_id X)
  map_comp f g := congrArg AddCommGrpCat.ofHom (triangulatedKZeroSourceMap_comp f g)

/-- 実際の BF 零次 K 群を加法記法で束ねた関手。 -/
def kZeroAdditiveFunctor : StableModel.{u} ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0))
  map f := AddCommGrpCat.ofHom (kHomotopyMap f 0).toAdditive
  map_id X := congrArg (fun h ↦ AddCommGrpCat.ofHom h.toAdditive) (kHomotopyMap_id X 0)
  map_comp f g := congrArg (fun h ↦ AddCommGrpCat.ofHom h.toAdditive) (kHomotopyMap_comp f g 0)

/-- 対象類を保つ三角圏 K₀ と BF 零次 K 群の可換群値自然同型。 -/
def triangulatedKZeroNatIso : triangulatedKZeroFunctor.{u} ≅ kZeroAdditiveFunctor.{u} :=
  NatIso.ofComponents (fun X ↦ (triangulatedKZeroEquiv X).toAddCommGrpIso) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro a
    exact triangulatedKZeroEquiv_naturality f a)

/-- 元の K 空間の π₀ と三角圏 K₀ の基礎集合の自然同型。 -/
def triangulatedKZeroPiZeroIso :
    triangulatedKZeroFunctor.{u} ⋙ forget AddCommGrpCat.{u} ≅ boundaryKPiZeroFunctor.{u} :=
  NatIso.ofComponents (fun X ↦
    ((triangulatedKZeroEquiv X).toEquiv.trans Additive.toMul |>.trans
      (kHomotopyZeroPiZeroEquiv X)).toIso) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro a
    have h := ConcreteCategory.congr_hom (kHomotopyZeroPiZeroIso.hom.naturality f)
      (triangulatedKZeroEquiv X a).toMul
    change kHomotopyZeroPiZeroEquiv Y
      (kHomotopyMap f 0 (triangulatedKZeroEquiv X a).toMul) =
      SSet.mapπ₀ (boundaryKSpaceFunctor.map f).right
        (kHomotopyZeroPiZeroEquiv X (triangulatedKZeroEquiv X a).toMul) at h
    change kHomotopyZeroPiZeroEquiv Y
      (triangulatedKZeroEquiv Y (triangulatedKZeroSourceMap f a)).toMul = _
    rw [triangulatedKZeroEquiv_naturality]
    exact h)

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Waldhausen "Thm §1.3" (partial := special) "仮定：安定準圏の実 K スペクトル（旧表の π₀K の安定準圏版）。結論：その π₀ とホモトピー三角圏の Grothendieck 群の自然同型（古典 wS• からの同定は別）。"] _root_.SerrePositivity.KST.SConstruction.triangulatedKZeroNatIso
