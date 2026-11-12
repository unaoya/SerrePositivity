module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpine
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialTelescopeShape

/-!
概要：望遠鏡の頂点族・区間族の写像を、元の可算 spine へ厳密に制限する。
方針：区間の全頂点は隣接する二番号に収まり、spine の任意の単体を一つの区間で覆える。
規約：元の可算 nerve への包含との合成を保持する。
使われ方：P-11 の望遠鏡と spine の strict な pushout 比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：一つの区間族の単体の可算番号は全頂点で一定。
方針：最初の頂点から指定頂点への射の離散成分を読む。
規約：端点の二元順序は変更しない。
使われ方：区間族の像が spine に入ることの確認。 -/
lemma sequentialTelescopeInterval_index_eq {d : ℕ}
    (s : ComposableArrows (Discrete (ULift.{u} ℕ) × Fin 2) d) (i : Fin (d + 1)) :
    (s.obj i).1.as = (s.obj 0).1.as :=
  (Discrete.eq_of_hom (s.map (homOfLE (Fin.zero_le i))).1).symm

/-- 概要：望遠鏡の離散頂点族を、元の可算 spine へ入れる。
方針：各単体の離散番号が一定であることを使う。
規約：可算 nerve への元の頂点写像を保持する。
使われ方：spine 上の望遠鏡の pushout の頂点側。 -/
def sequentialTelescopeVertexToSpine :
    nerve (Discrete (ULift.{u} ℕ)) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.{u} : SSet.{u}) where
  app n := ↾fun s ↦ ⟨(nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}).app n s, by
    intro i j
    change (s.obj j).as.down ≤ (s.obj i).as.down + 1
    have hi := Discrete.eq_of_hom (s.map (homOfLE (Fin.zero_le i)))
    have hj := Discrete.eq_of_hom (s.map (homOfLE (Fin.zero_le j)))
    rw [← hi, ← hj]
    omega⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl

/-- 概要：望遠鏡の離散区間族を、元の可算 spine へ写す。
方針：可算番号の定値性と、二元順序の頂点番号の範囲を使う。
規約：全区間の全退化単体を含めて写す。
使われ方：spine 上の望遠鏡の pushout の区間側。 -/
def sequentialTelescopeIntervalToSpine :
    nerve (Discrete (ULift.{u} ℕ) × Fin 2) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.{u} : SSet.{u}) where
  app n := ↾fun s ↦ ⟨(nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u}).app n s, by
    intro i j
    change (s.obj j).1.as.down + (s.obj j).2.val ≤
      (s.obj i).1.as.down + (s.obj i).2.val + 1
    rw [sequentialTelescopeInterval_index_eq s i, sequentialTelescopeInterval_index_eq s j]
    have hi := (s.obj i).2.isLt
    have hj := (s.obj j).2.isLt
    omega⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl

/-- 概要：spine へ制限した頂点写像は、包含後に元の nerve 写像を回収する。
方針：部分型の値を忘れる。
規約：全単体集合写像の等式。
使われ方：strict な pushout 比較。 -/
lemma sequentialTelescopeVertexToSpine_ι :
    sequentialTelescopeVertexToSpine.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.ι =
      nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u} := rfl

/-- 概要：spine へ制限した区間写像は、包含後に元の nerve 写像を回収する。
方針：部分型の値を忘れる。
規約：全単体集合写像の等式。
使われ方：strict な pushout 比較。 -/
lemma sequentialTelescopeIntervalToSpine_ι :
    sequentialTelescopeIntervalToSpine.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.ι =
      nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u} := rfl

/-- 概要：離散頂点族から spine への写像は単射。
方針：元の可算 nerve への写像の単射性を包含との合成から反映する。
規約：区間族の写像の単射性は要求しない。
使われ方：spine の shape pushout の次数ごとの判定。 -/
instance sequentialTelescopeVertexToSpine_mono : Mono sequentialTelescopeVertexToSpine.{u} := by
  have hv : Mono (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveMap_mono_of_faithful _ (fun _ _ h ↦ Discrete.ext h)
  have : Mono (sequentialTelescopeVertexToSpine.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.ι) := hv
  exact mono_of_mono sequentialTelescopeVertexToSpine _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.ι

/-- 概要：spine へ制限した頂点族と区間族は両端点上で厳密に一致する。
方針：spine の単射な包含後に、元の関手の整合条件を使う。
規約：同型だけではなく射の等式。
使われ方：望遠鏡の pushout からの降下。 -/
lemma sequentialTelescopeToSpine_condition :
    nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeAttachFunctor.{u} ≫ sequentialTelescopeVertexToSpine =
      nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u} ≫ sequentialTelescopeIntervalToSpine := by
  apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.ι).mp
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeAttachFunctor.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}) =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u})
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeFunctor_condition]

/-- 概要：望遠鏡全体から元の可算 spine への一つの写像。
方針：端点上で一致する頂点族・区間族を strict pushout へ降ろす。
規約：元の望遠鏡形状を保持する。
使われ方：可算 nerve への写像を spine 包含で因子化する。 -/
def sequentialTelescopeToSpine : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeShape.{u} ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.{u} : SSet.{u}) :=
  pushout.desc sequentialTelescopeVertexToSpine sequentialTelescopeIntervalToSpine
    sequentialTelescopeToSpine_condition

/-- 概要：望遠鏡から可算 nerve への写像は、元の spine を通って因子化する。
方針：pushout の両側への制限を比較する。
規約：前に構成した同じ可算 nerve への写像を回収する。
使われ方：spine 包含の inner anodyne 性の望遠鏡への移送。 -/
lemma sequentialTelescopeToSpine_ι :
    sequentialTelescopeToSpine.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.ι = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve.{u} := by
  apply pushout.hom_ext
  · simp only [sequentialTelescopeToSpine, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve,
      pushout.inl_desc_assoc, pushout.inl_desc, sequentialTelescopeVertexToSpine_ι]
  · simp only [sequentialTelescopeToSpine, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve,
      pushout.inr_desc_assoc, pushout.inr_desc, sequentialTelescopeIntervalToSpine_ι]

/-- 概要：spine の任意の全単体は、望遠鏡の一つの区間族の単体で覆える。
方針：最初の頂点を区間番号とし、各頂点との差を二元順序の頂点として読む。
規約：退化単体も含めて次数ごとの全射性を主張する。
使われ方：望遠鏡から spine への strict な同型の全射部分。 -/
lemma sequentialTelescopeIntervalToSpine_surjective (d : ℕ) :
    Function.Surjective (sequentialTelescopeIntervalToSpine.{u}.app (Opposite.op ⦋d⦌)) := by
  intro s
  let n := (s.val.obj 0).down
  let f (i : Fin (d + 1)) : Fin 2 :=
    ⟨(s.val.obj i).down - n, by have h := s.property 0 i; dsimp [n]; omega⟩
  have hf : Monotone f := by
    intro i j hij
    have h := s.val.monotone hij
    change (s.val.obj i).down - n ≤ (s.val.obj j).down - n
    exact Nat.sub_le_sub_right h n
  let b := hf.functor ⋙ CategoryTheory.Prod.sectR (Discrete.mk (ULift.up n : ULift.{u} ℕ)) (Fin 2)
  refine ⟨b, Subtype.ext ?_⟩
  change b ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u} = s.val
  exact CategoryTheory.Functor.ext (fun i ↦ ULift.ext (by
    change n + ((s.val.obj i).down - n) = (s.val.obj i).down
    exact Nat.add_sub_of_le (s.val.monotone (Fin.zero_le i))))
    (fun _ _ _ ↦ Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
