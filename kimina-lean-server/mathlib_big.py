
# codex="""
# import Mathlib.Data.Set.Function
# import Mathlib.Logic.Equiv.Defs
# import Mathlib.Tactic.Core
# import Mathlib.Tactic.Attr.Core

# #align_import logic.equiv.local_equiv from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

# open Lean Meta Elab Tactic

# def mfld_cfg : Simps.Config where
#   attrs := [`mfld_simps]
#   fullyApplied := false
# #align mfld_cfg mfld_cfg

# namespace Tactic.MfldSetTac

# elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
#   let g ← getMainGoal
#   let goalTy := (← instantiateMVars (← g.getDecl).type).getAppFnArgs
#   match goalTy with
#   | (``Eq, #[_ty, _e₁, _e₂]) =>
#     evalTactic (← `(tactic| (
#       apply Set.ext; intro my_y
#       constructor <;>
#         · intro h_my_y
#           try simp only [*, mfld_simps] at h_my_y
#           try simp only [*, mfld_simps])))
#   | (``Subset, #[_ty, _inst, _e₁, _e₂]) =>
#     evalTactic (← `(tactic| (
#       intro my_y h_my_y
#       try simp only [*, mfld_simps] at h_my_y
#       try simp only [*, mfld_simps])))
#   | _ => throwError "goal should be an equality or an inclusion"

# attribute [mfld_simps] and_true eq_self_iff_true Function.comp_apply

# end Tactic.MfldSetTac

# open Function Set

# variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}


# structure PartialEquiv (α : Type*) (β : Type*) where
 
#   toFun : α → β
#   invFun : β → α
#   source : Set α
#   target : Set β
#   map_source' : ∀ ⦃x⦄, x ∈ source → toFun x ∈ target
#   map_target' : ∀ ⦃x⦄, x ∈ target → invFun x ∈ source
#   left_inv' : ∀ ⦃x⦄, x ∈ source → invFun (toFun x) = x
#   right_inv' : ∀ ⦃x⦄, x ∈ target → toFun (invFun x) = x
# #align local_equiv PartialEquiv

# attribute [coe] PartialEquiv.toFun

# namespace PartialEquiv

# variable (e : PartialEquiv α β) (e' : PartialEquiv β γ)

# instance [Inhabited α] [Inhabited β] : Inhabited (PartialEquiv α β) :=
#   ⟨⟨const α default, const β default, ∅, ∅, mapsTo_empty _ _, mapsTo_empty _ _, eqOn_empty _ _,
#       eqOn_empty _ _⟩⟩

# @[symm]
# protected def symm : PartialEquiv β α where
#   toFun := e.invFun
#   invFun := e.toFun
#   source := e.target
#   target := e.source
#   map_source' := e.map_target'
#   map_target' := e.map_source'
#   left_inv' := e.right_inv'
#   right_inv' := e.left_inv'
# #align local_equiv.symm PartialEquiv.symm

# instance : CoeFun (PartialEquiv α β) fun _ => α → β :=
#   ⟨PartialEquiv.toFun⟩

# def Simps.symm_apply (e : PartialEquiv α β) : β → α :=
#   e.symm
# #align local_equiv.simps.symm_apply PartialEquiv.Simps.symm_apply

# initialize_simps_projections PartialEquiv (toFun → apply, invFun → symm_apply)

# #noalign local_equiv.coe_mk

# @[simp, mfld_simps]
# theorem coe_symm_mk (f : α → β) (g s t ml mr il ir) :
#     ((PartialEquiv.mk f g s t ml mr il ir).symm : β → α) = g :=
#   rfl
# #align local_equiv.coe_symm_mk PartialEquiv.coe_symm_mk

# #noalign local_equiv.to_fun_as_coe

# @[simp, mfld_simps]
# theorem invFun_as_coe : e.invFun = e.symm :=
#   rfl
# #align local_equiv.inv_fun_as_coe PartialEquiv.invFun_as_coe

# @[simp, mfld_simps]
# theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
#   e.map_source' h
# #align local_equiv.map_source PartialEquiv.map_source

# lemma map_source'' : e '' e.source ⊆ e.target :=
#   fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

# @[simp, mfld_simps]
# theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
#   e.map_target' h
# #align local_equiv.map_target PartialEquiv.map_target

# @[simp, mfld_simps]
# theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
#   e.left_inv' h
# #align local_equiv.left_inv PartialEquiv.left_inv

# @[simp, mfld_simps]
# theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
#   e.right_inv' h
# #align local_equiv.right_inv PartialEquiv.right_inv

# theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
#     x = e.symm y ↔ e x = y :=
#   ⟨fun h => by rw [← e.right_inv hy, h], fun h => by rw [← e.left_inv hx, h]⟩
# #align local_equiv.eq_symm_apply PartialEquiv.eq_symm_apply

# protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source
# #align local_equiv.maps_to PartialEquiv.mapsTo

# theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
#   e.symm.mapsTo
# #align local_equiv.symm_maps_to PartialEquiv.symm_mapsTo

# protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv
# #align local_equiv.left_inv_on PartialEquiv.leftInvOn

# protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv
# #align local_equiv.right_inv_on PartialEquiv.rightInvOn

# protected theorem invOn : InvOn e.symm e e.source e.target :=
#   ⟨e.leftInvOn, e.rightInvOn⟩
# #align local_equiv.inv_on PartialEquiv.invOn

# protected theorem injOn : InjOn e e.source :=
#   e.leftInvOn.injOn
# #align local_equiv.inj_on PartialEquiv.injOn

# protected theorem bijOn : BijOn e e.source e.target :=
#   e.invOn.bijOn e.mapsTo e.symm_mapsTo
# #align local_equiv.bij_on PartialEquiv.bijOn

# protected theorem surjOn : SurjOn e e.source e.target :=
#   e.bijOn.surjOn
# #align local_equiv.surj_on PartialEquiv.surjOn

# @[simps (config := .asFn)]
# def _root_.Equiv.toPartialEquivOfImageEq (e : α ≃ β) (s : Set α) (t : Set β) (h : e '' s = t) :
#     PartialEquiv α β where
#   toFun := e
#   invFun := e.symm
#   source := s
#   target := t
#   map_source' x hx := h ▸ mem_image_of_mem _ hx
#   map_target' x hx := by
#     subst t
#     rcases hx with ⟨x, hx, rfl⟩
#     rwa [e.symm_apply_apply]
#   left_inv' x _ := e.symm_apply_apply x
#   right_inv' x _ := e.apply_symm_apply x

# @[simps! (config := mfld_cfg)]
# def _root_.Equiv.toPartialEquiv (e : α ≃ β) : PartialEquiv α β :=
#   e.toPartialEquivOfImageEq univ univ <| by rw [image_univ, e.surjective.range_eq]
# #align equiv.to_local_equiv Equiv.toPartialEquiv
# #align equiv.to_local_equiv_symm_apply Equiv.toPartialEquiv_symm_apply
# #align equiv.to_local_equiv_target Equiv.toPartialEquiv_target
# #align equiv.to_local_equiv_apply Equiv.toPartialEquiv_apply
# #align equiv.to_local_equiv_source Equiv.toPartialEquiv_source

# instance inhabitedOfEmpty [IsEmpty α] [IsEmpty β] : Inhabited (PartialEquiv α β) :=
#   ⟨((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).toPartialEquiv⟩
# #align local_equiv.inhabited_of_empty PartialEquiv.inhabitedOfEmpty

# /-- Create a copy of a `PartialEquiv` providing better definitional equalities. -/
# @[simps (config := .asFn)]
# def copy (e : PartialEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g) (s : Set α)
#     (hs : e.source = s) (t : Set β) (ht : e.target = t) :
#     PartialEquiv α β where
#   toFun := f
#   invFun := g
#   source := s
#   target := t
#   map_source' _ := ht ▸ hs ▸ hf ▸ e.map_source
#   map_target' _ := hs ▸ ht ▸ hg ▸ e.map_target
#   left_inv' _ := hs ▸ hf ▸ hg ▸ e.left_inv
#   right_inv' _ := ht ▸ hf ▸ hg ▸ e.right_inv
# #align local_equiv.copy PartialEquiv.copy
# #align local_equiv.copy_source PartialEquiv.copy_source
# #align local_equiv.copy_apply PartialEquiv.copy_apply
# #align local_equiv.copy_symm_apply PartialEquiv.copy_symm_apply
# #align local_equiv.copy_target PartialEquiv.copy_target

# theorem copy_eq (e : PartialEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g)
#     (s : Set α) (hs : e.source = s) (t : Set β) (ht : e.target = t) :
#     e.copy f hf g hg s hs t ht = e := by
#   substs f g s t
#   cases e
#   rfl
# #align local_equiv.copy_eq PartialEquiv.copy_eq

# /-- Associate to a `PartialEquiv` an `Equiv` between the source and the target. -/
# protected def toEquiv : e.source ≃ e.target where
#   toFun x := ⟨e x, e.map_source x.mem⟩
#   invFun y := ⟨e.symm y, e.map_target y.mem⟩
#   left_inv := fun ⟨_, hx⟩ => Subtype.eq <| e.left_inv hx
#   right_inv := fun ⟨_, hy⟩ => Subtype.eq <| e.right_inv hy
# #align local_equiv.to_equiv PartialEquiv.toEquiv

# @[simp, mfld_simps]
# theorem symm_source : e.symm.source = e.target :=
#   rfl
# #align local_equiv.symm_source PartialEquiv.symm_source

# @[simp, mfld_simps]
# theorem symm_target : e.symm.target = e.source :=
#   rfl
# #align local_equiv.symm_target PartialEquiv.symm_target

# @[simp, mfld_simps]
# theorem symm_symm : e.symm.symm = e := by
#   cases e
#   rfl
# #align local_equiv.symm_symm PartialEquiv.symm_symm

# theorem symm_bijective :
#     Function.Bijective (PartialEquiv.symm : PartialEquiv α β → PartialEquiv β α) :=
#   Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

# theorem image_source_eq_target : e '' e.source = e.target :=
#   e.bijOn.image_eq
# #align local_equiv.image_source_eq_target PartialEquiv.image_source_eq_target

# theorem forall_mem_target {p : β → Prop} : (∀ y ∈ e.target, p y) ↔ ∀ x ∈ e.source, p (e x) := by
#   rw [← image_source_eq_target, forall_mem_image]
# #align local_equiv.forall_mem_target PartialEquiv.forall_mem_target

# theorem exists_mem_target {p : β → Prop} : (∃ y ∈ e.target, p y) ↔ ∃ x ∈ e.source, p (e x) := by
#   rw [← image_source_eq_target, exists_mem_image]
# #align local_equiv.exists_mem_target PartialEquiv.exists_mem_target

# /-- We say that `t : Set β` is an image of `s : Set α` under a partial equivalence if
# any of the following equivalent conditions hold:

# * `e '' (e.source ∩ s) = e.target ∩ t`;
# * `e.source ∩ e ⁻¹ t = e.source ∩ s`;
# * `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
# -/
# def IsImage (s : Set α) (t : Set β) : Prop :=
#   ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
# #align local_equiv.is_image PartialEquiv.IsImage



# namespace IsImage

# variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

# theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
#   h hx
# #align local_equiv.is_image.apply_mem_iff PartialEquiv.IsImage.apply_mem_iff

# theorem symm_apply_mem_iff (h : e.IsImage s t) : ∀ ⦃y⦄, y ∈ e.target → (e.symm y ∈ s ↔ y ∈ t) :=
#   e.forall_mem_target.mpr fun x hx => by rw [e.left_inv hx, h hx]
# #align local_equiv.is_image.symm_apply_mem_iff PartialEquiv.IsImage.symm_apply_mem_iff

# protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
#   h.symm_apply_mem_iff
# #align local_equiv.is_image.symm PartialEquiv.IsImage.symm

# @[simp]
# theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
#   ⟨fun h => h.symm, fun h => h.symm⟩
# #align local_equiv.is_image.symm_iff PartialEquiv.IsImage.symm_iff

# protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
#   fun _ hx => ⟨e.mapsTo hx.1, (h hx.1).2 hx.2⟩
# #align local_equiv.is_image.maps_to PartialEquiv.IsImage.mapsTo

# theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
#   h.symm.mapsTo
# #align local_equiv.is_image.symm_maps_to PartialEquiv.IsImage.symm_mapsTo

# /-- Restrict a `PartialEquiv` to a pair of corresponding sets. -/
# @[simps (config := .asFn)]
# def restr (h : e.IsImage s t) : PartialEquiv α β where
#   toFun := e
#   invFun := e.symm
#   source := e.source ∩ s
#   target := e.target ∩ t
#   map_source' := h.mapsTo
#   map_target' := h.symm_mapsTo
#   left_inv' := e.leftInvOn.mono inter_subset_left
#   right_inv' := e.rightInvOn.mono inter_subset_left
# #align local_equiv.is_image.restr PartialEquiv.IsImage.restr
# #align local_equiv.is_image.restr_apply PartialEquiv.IsImage.restr_apply
# #align local_equiv.is_image.restr_source PartialEquiv.IsImage.restr_source
# #align local_equiv.is_image.restr_target PartialEquiv.IsImage.restr_target
# #align local_equiv.is_image.restr_symm_apply PartialEquiv.IsImage.restr_symm_apply


# theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s := by
#   simp only [IsImage, ext_iff, mem_inter_iff, mem_preimage, and_congr_right_iff]
# #align local_equiv.is_image.iff_preimage_eq PartialEquiv.IsImage.iff_preimage_eq

# alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq
# #align local_equiv.is_image.of_preimage_eq PartialEquiv.IsImage.of_preimage_eq
# #align local_equiv.is_image.preimage_eq PartialEquiv.IsImage.preimage_eq

# theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
#   symm_iff.symm.trans iff_preimage_eq
# #align local_equiv.is_image.iff_symm_preimage_eq PartialEquiv.IsImage.iff_symm_preimage_eq

# alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq
# #align local_equiv.is_image.of_symm_preimage_eq PartialEquiv.IsImage.of_symm_preimage_eq
# #align local_equiv.is_image.symm_preimage_eq PartialEquiv.IsImage.symm_preimage_eq

# end IsImage

# /-- Restricting a partial equivalence to `e.source ∩ s` -/
# protected def restr (s : Set α) : PartialEquiv α β :=
#   (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr
# #align local_equiv.restr PartialEquiv.restr


# /-- The identity partial equiv -/
# protected def refl (α : Type*) : PartialEquiv α α :=
#   (Equiv.refl α).toPartialEquiv
# #align local_equiv.refl PartialEquiv.refl

# @[mfld_simps]
# theorem refl_restr_target (s : Set α) : ((PartialEquiv.refl α).restr s).target = s := by
#   change univ ∩ id ⁻¹' s = s
#   simp
# """
