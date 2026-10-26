module
public import SerrePositivity.KST.SConstruction.DGModuleConeHomotopyTriangle
public import SerrePositivity.DifferentialGraded.Module.ConeRotationHomotopy

/-!
概要：元 connecting 射の実 cone から元終域の shift への指定比較を作る。
方針：元回転比較の指定ホモトピーから実 cone 射を作り、二回目の元回転逆を合成する。
規約：元実 cone と元指定ホモトピーを保持。使われ方：実逆回転後の商合成の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {M N : ModuleCategory R D} (f : M ⟶ N)

/-- 概要：元 connecting と一回目の実回転比較の指定可換ホモトピー。
方針：元の全加群 Hom end 内の同じ次数 −1 元を使う。
規約：元指定元を保持。使われ方：実 cone 射の入力。 -/
def dgModuleConnectingConeSquareHomotopy : ModuleHomotopy R D
    (moduleConeConnecting R D f ≫ moduleConeRotationHom R D f)
    ((𝟙 (moduleCone R D f)) ≫ moduleConeInr R D (moduleConeInr R D f)) := by
  simpa only [Category.id_comp] using moduleConeRotationConnectingHomotopy R D f

/-- 概要：connecting 射の実 cone を二回転目の実 cone へ送る同じ実射。
方針：元二辺と元指定可換ホモトピーを実 cone 射へ渡す。
規約：元の cone 対象を選び直さない。使われ方：同じ逆回転比較の第一段。 -/
def dgModuleConnectingConeMap :
    moduleCone R D (moduleConeConnecting R D f) ⟶
      moduleCone R D (moduleConeInr R D (moduleConeInr R D f)) :=
  moduleConeMapOfHomotopy R D (moduleConeConnecting R D f)
    (moduleConeInr R D (moduleConeInr R D f)) (𝟙 _) (moduleConeRotationHom R D f)
    (dgModuleConnectingConeSquareHomotopy R D f)

/-- 概要：同じ connecting cone 射は元 K(D) で同値。
方針：恒等と元一回転同値を保持する標準三角形の写像を使う。
規約：元の実射の判定。使われ方：実合成比較の可逆性。 -/
lemma dgModuleConnectingConeMap_isIso :
    IsIso ((moduleToHomotopy R D).map (dgModuleConnectingConeMap R D f)) := by
  apply dgModuleConeMapOfHomotopy_isIso
  · rw [CategoryTheory.Functor.map_id]
    infer_instance
  · exact (moduleConeRotationHomotopyIso R D f).isIso_hom

/-- 概要：同じ connecting cone から元終域 shift への指定実加群比較。
方針：元実 cone 射と二回転目の元実逆射を合成する。
規約：対象別の存在選択を使わない。使われ方：実逆回転後の合成比較の元射。 -/
def dgModuleConnectingConeComparison :
    moduleCone R D (moduleConeConnecting R D f) ⟶ moduleShiftObj R D 1 N :=
  dgModuleConnectingConeMap R D f ≫ moduleConeRotationInv R D (moduleConeInr R D f)

/-- 概要：指定された同じ connecting cone 比較は K(D) で同値。
方針：元 cone 射と二回転目の元回転同値の可逆性を合成する。
規約：元射を変更しない。使われ方：逆 shift 後の実比較の判定。 -/
lemma dgModuleConnectingConeComparison_isIso :
    IsIso ((moduleToHomotopy R D).map (dgModuleConnectingConeComparison R D f)) := by
  letI := dgModuleConnectingConeMap_isIso R D f
  haveI : IsIso ((moduleToHomotopy R D).map
      (moduleConeRotationInv R D (moduleConeInr R D f))) :=
    (moduleConeRotationHomotopyIso R D (moduleConeInr R D f)).isIso_inv
  rw [dgModuleConnectingConeComparison, CategoryTheory.Functor.map_comp]
  infer_instance

/-- 概要：元一回転逆射は同じ標準包含の後で元 connecting 射を回収する。
方針：元の指定 boundary 延長の包含回収を使う。
規約：実射の等号。使われ方：逆回転後の合成三角形の符号照合。 -/
lemma dgModuleConeRotationInv_inr :
    moduleConeInr R D (moduleConeInr R D f) ≫ moduleConeRotationInv R D f =
      moduleConeConnecting R D f :=
  moduleConeDescOfBoundary_inr R D _ _ _ _

/-- 概要：同じ connecting cone 比較の包含制限は元射 shift の負。
方針：元 cone 射の包含回収と二回転目の元逆射・元回転式を合成する。
規約：符号を保持。使われ方：指定上二単体の境界計算。 -/
lemma dgModuleConnectingConeComparison_inr :
    moduleConeInr R D (moduleConeConnecting R D f) ≫
      dgModuleConnectingConeComparison R D f = -f⟦(1 : ℤ)⟧' := by
  let c := moduleConeRotationInv R D (moduleConeInr R D f)
  have h := moduleConeMapOfHomotopy_inr R D (moduleConeConnecting R D f)
    (moduleConeInr R D (moduleConeInr R D f)) (𝟙 _) (moduleConeRotationHom R D f)
    (dgModuleConnectingConeSquareHomotopy R D f)
  change moduleConeInr R D (moduleConeConnecting R D f) ≫
    (dgModuleConnectingConeMap R D f ≫ c) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ c) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => moduleConeRotationHom R D f ≫ k)
          (dgModuleConeRotationInv_inr R D (moduleConeInr R D f))).trans
            (moduleConeRotation_connecting R D f))))

end SerrePositivity.KST.SConstruction
