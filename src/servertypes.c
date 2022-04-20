#include <stdlib.h>
#include <stdio.h>

#include "servertypes.h"

static struct maildir_type_list *type_list = NULL;

static
void maildir_type_list_prepend(struct maildir_type_list **list, const struct maildir_type *type)
{
	struct maildir_type_list *t = malloc(sizeof(struct maildir_type_list));
	if (!t) {
		perror("malloc");
		exit(1);
	}

	t->type = type;
	t->pvt = NULL;
	t->next = *list;
	*list = t;
}

void register_maildir_type(const struct maildir_type* type)
{
	maildir_type_list_prepend(&type_list, type);
}

struct maildir_type_list* maildir_find_type(const char* folder)
{
	const struct maildir_type_list* test = type_list;
	struct maildir_type_list *result = NULL;

	while(test) {
		if (test->type->detect(folder))
			maildir_type_list_prepend(&result, test->type);
		test = test->next;
	}

	return result;
}

static
void __attribute__((destructor)) deinit()
{
	maildir_type_list_free(type_list);
}
