module
public import SerrePositivity.KST.SConstruction.Cofinality.CutKZeroEquiv

/-!
概要：同じ指定射の S_n K₀ 余核に元の端点制限を降ろす。
方針：元の完全射の自然性により分母の像が保存されることを確認する。
規約：完備化の仮定を使わず、元の射の像で割る。
使われ方：障害余核の S 方向の加法的分解。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：元の S_n 射の三角圏 K₀ 余核。
方針：元の標的 K₀ を元の始域の像で割る。
規約：同じ n と指定射を保持する。
使われ方：区間分解の群。 -/
abbrev cutKZeroCokernel (n : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :=
  TriangulatedK0 (hoFunctor.obj (sStableModel n Y).carrier) ⧸
    (triangulatedKZeroSourceMap ((sEndofunctor n).map f)).range

/-- 概要：元の指定射に関する区間制限の K₀ 自然性。
方針：S 自己関手間の元の自然変換に K₀ の合成則を適用する。
規約：完全射の底は元の端点制限。
使われ方：分母の像の保存。 -/
lemma cutKZeroRestriction_naturality {m n : ℕ} {X Y : StableModel.{u}} (f : X ⟶ Y)
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    (cutKZeroRestriction Y θ).comp (triangulatedKZeroSourceMap ((sEndofunctor n).map f)) =
      (triangulatedKZeroSourceMap ((sEndofunctor m).map f)).comp (cutKZeroRestriction X θ) :=
  (triangulatedKZeroSourceMap_comp _ _).symm.trans
    ((congrArg triangulatedKZeroSourceMap ((sEndofunctorMap θ).naturality f)).trans
      (triangulatedKZeroSourceMap_comp _ _))

/-- 概要：区間制限は元の K₀ 像を保存する。
方針：K₀ の自然性で元の始域の制限を持ち上げとして使う。
規約：追加の単射性や全射性の仮定を入れない。
使われ方：余核写像の定義条件。 -/
lemma cutKZeroRestriction_range {m n : ℕ} {X Y : StableModel.{u}} (f : X ⟶ Y)
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    (triangulatedKZeroSourceMap ((sEndofunctor n).map f)).range ≤
      ((triangulatedKZeroSourceMap ((sEndofunctor m).map f)).range).comap
        (cutKZeroRestriction Y θ) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨cutKZeroRestriction X θ a,
    (DFunLike.congr_fun (cutKZeroRestriction_naturality f θ) a).symm⟩

/-- 概要：元の区間制限の K₀ 余核への作用。
方針：分母の像の保存によって元の誘導準同型を降ろす。
規約：指定した射の像で割る。
使われ方：余核の面・退化と延長。 -/
def cutCokernelRestriction {m n : ℕ} {X Y : StableModel.{u}} (f : X ⟶ Y)
    (θ : Fin (m + 1) →o Fin (n + 1)) : cutKZeroCokernel n f →+ cutKZeroCokernel m f :=
  QuotientAddGroup.map (triangulatedKZeroSourceMap ((sEndofunctor n).map f)).range
    (triangulatedKZeroSourceMap ((sEndofunctor m).map f)).range
    (cutKZeroRestriction Y θ) (cutKZeroRestriction_range f θ)

/-- 概要：余核の区間作用の元の代表上の式。
方針：商写像の定義を使う。
規約：元の K₀ の代表を保つ。
使われ方：余核上の厳密な関係式の検査。 -/
lemma cutCokernelRestriction_mk {m n : ℕ} {X Y : StableModel.{u}} (f : X ⟶ Y)
    (θ : Fin (m + 1) →o Fin (n + 1))
    (a : TriangulatedK0 (hoFunctor.obj (sStableModel n Y).carrier)) :
    cutCokernelRestriction f θ (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (cutKZeroRestriction Y θ a) := rfl

end SerrePositivity.KST.SConstruction.Cofinality
