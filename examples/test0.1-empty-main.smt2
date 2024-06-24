(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)


(check-sat)
(get-model)
