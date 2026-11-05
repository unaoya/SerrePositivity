module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CoherentArrowStrings

/-! # 合成列の精密化から元の Path の高次族を構成する
概要：精密化の列を、最後の元の合成列内の増大する Path の実単体へ写す。
方針：各再添字の像を元の native な Path とし、精密化の合成で包含を得る。
規約：高次単体ごとに円柱を追加仮定せず、元の再添字から全 Path 単体を直接作る。
使われ方：元の coherent K prism の豊穣作用を共通の合成列パラメータで評価する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open scoped _root_.Simplicial
variable {I : Type u} [SmallCategory I] {x y : I} {f : x ⟶ y}

/-- 精密化の再添字の像を、元の合成列内の端点を保つ native な Path とする。 -/
def coherentStringRefinementPath {s t : CoherentArrowString f} (a : s ⟶ t) :
    Path (ULift.up 0 : ULift.{u} (Fin (t.length + 1))) (ULift.up (Fin.last t.length)) where
  I := Set.range (fun i => ULift.up (a.map.toOrderHom i))
  left := ⟨0, congrArg ULift.up a.first⟩
  right := ⟨Fin.last s.length, congrArg ULift.up a.last⟩
  left_le _ _ := Fin.zero_le _
  le_right _ _ := Fin.le_last _

/-- 同じ精密化に沿って、元の全端点 Path を像の Path へ写す。 -/
def coherentStringPathReindex {s t : CoherentArrowString f} (a : s ⟶ t)
    (p : Path (ULift.up 0 : ULift.{u} (Fin (s.length + 1))) (ULift.up (Fin.last s.length))) :
    Path (ULift.up 0 : ULift.{u} (Fin (t.length + 1))) (ULift.up (Fin.last t.length)) where
  I := a.map.toOrderHom.uliftMap '' p.I
  left := ⟨ULift.up 0, p.left, congrArg ULift.up a.first⟩
  right := ⟨ULift.up (Fin.last s.length), p.right, congrArg ULift.up a.last⟩
  left_le _ _ := Fin.zero_le _
  le_right _ _ := Fin.le_last _

/-- 元の Path の全包含も同時に再添字する関手。 -/
def coherentStringPathReindexFunctor {s t : CoherentArrowString f} (a : s ⟶ t) :
    Path (ULift.up 0 : ULift.{u} (Fin (s.length + 1))) (ULift.up (Fin.last s.length)) ⥤
    Path (ULift.up 0 : ULift.{u} (Fin (t.length + 1))) (ULift.up (Fin.last t.length)) where
  obj := coherentStringPathReindex a
  map b := ⟨⟨⟨Set.image_mono b.1.1.1⟩⟩⟩

/-- 精密化の合成の Path は、元の前半の Path を後半で再添字したもの。 -/
lemma coherentStringRefinementPath_comp {s t r : CoherentArrowString f}
    (a : s ⟶ t) (b : t ⟶ r) :
    coherentStringRefinementPath (a ≫ b) =
      coherentStringPathReindex b (coherentStringRefinementPath a) := by
  apply SimplicialThickening.Path.ext
  ext q
  change (∃ i, ULift.up (b.map.toOrderHom (a.map.toOrderHom i)) = q) ↔
    ∃ z, (∃ i, ULift.up (a.map.toOrderHom i) = z) ∧
      b.map.toOrderHom.uliftMap z = q
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨ULift.up (a.map.toOrderHom i), ⟨i, rfl⟩, hi⟩
  · rintro ⟨z, ⟨i, rfl⟩, hi⟩
    exact ⟨i, hi⟩

/-- 二つの連続した精密化から得る、元の最後の合成列内の Path の包含。 -/
def coherentStringRefinementPathInclusion {s t r : CoherentArrowString f}
    (a : s ⟶ t) (b : t ⟶ r) :
    coherentStringRefinementPath (a ≫ b) ⟶ coherentStringRefinementPath b := by
  refine ⟨⟨⟨?_⟩⟩⟩
  rintro q ⟨i, hi⟩
  exact ⟨a.map.toOrderHom i, hi⟩

/-- 精密化の高次単体から、最後の元の合成列内の全 Path の単体を直接作る。 -/
def coherentStringPathFlag {n : ℕ} (F : (nerve (CoherentArrowString f)) _⦋n⦌) :
    (nerve (Path (ULift.up 0 : ULift.{u} (Fin ((F.obj (Fin.last n)).length + 1)))
      (ULift.up (Fin.last (F.obj (Fin.last n)).length)))) _⦋n⦌ where
  obj i := coherentStringRefinementPath (F.map (homOfLE (Fin.le_last i)))
  map {i j} a := by
    have hc : F.map a ≫ F.map (homOfLE (Fin.le_last j)) =
        F.map (homOfLE (Fin.le_last i)) := by
      rw [← CategoryTheory.Functor.map_comp]
      congr 1
    exact eqToHom (congrArg coherentStringRefinementPath hc).symm ≫
      coherentStringRefinementPathInclusion (F.map a) (F.map (homOfLE (Fin.le_last j)))
  map_id _ := by
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _
  map_comp _ _ := by
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

/-- 全単体作用による最後の合成列の変化も、同じ元の精密化による Path の像として一致。 -/
lemma coherentStringPathFlag_naturality {m n : ℕ}
    (F : (nerve (CoherentArrowString f)) _⦋n⦌) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (nerveMap (coherentStringPathReindexFunctor
      (F.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).app (Opposite.op ⦋m⦌)
      (coherentStringPathFlag ((nerve (CoherentArrowString f)).map θ.op F)) =
    (nerve (Path (ULift.up 0 : ULift.{u} (Fin ((F.obj (Fin.last n)).length + 1)))
      (ULift.up (Fin.last (F.obj (Fin.last n)).length)))).map θ.op
      (coherentStringPathFlag F) := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · change coherentStringPathReindex
      (F.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))
      (coherentStringRefinementPath
        (F.map (θ.toOrderHom.monotone.functor.map (homOfLE (Fin.le_last i))))) =
      coherentStringRefinementPath (F.map (homOfLE (Fin.le_last (θ.toOrderHom i))))
    rw [← coherentStringRefinementPath_comp]
    apply congrArg coherentStringRefinementPath
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
  · intro i j a
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathFlag := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathFlag_naturality := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag_naturality

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindex := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindex

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindexFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindexFunctor := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindexFunctor

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPath (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringRefinementPath := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPath

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPathInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringRefinementPathInclusion := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPathInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringRefinementPath_comp := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPath_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathFlag._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathFlag._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathFlag._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathFlag._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathFlag._proof_5 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathFlag._proof_6 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathFlag._proof_7 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathFlag._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindex._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindex._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindex._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindex._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindex._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindex._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindex._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindexFunctor._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindexFunctor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindexFunctor._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindexFunctor._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindexFunctor._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringPathReindexFunctor._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringRefinementPath._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPath._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringRefinementPath._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPath._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringRefinementPath._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPath._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringRefinementPath._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPath._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringRefinementPath._proof_5 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPath._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringRefinementPathInclusion._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.coherentStringRefinementPathInclusion._proof_1
